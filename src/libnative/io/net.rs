// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cast;
use std::io::net::ip;
use std::io;
use std::libc;
use std::mem;
use std::rt::rtio;
use std::unstable::intrinsics;

use super::IoResult;
use super::file::{FileDesc, CloseSocket};

pub struct TcpStream {
    priv fd: FileDesc,
}

#[cfg(target_endian = "big")] pub fn htons(x: u16) -> u16 { x }
#[cfg(target_endian = "big")] pub fn ntohs(x: u16) -> u16 { x }
#[cfg(target_endian = "little")]
pub fn htons(u: u16) -> u16 {
    unsafe { intrinsics::bswap16(u as i16) as u16 }
}
#[cfg(target_endian = "little")]
pub fn ntohs(u: u16) -> u16 {
    unsafe { intrinsics::bswap16(u as i16) as u16 }
}

#[cfg(windows)] pub type sock_t = libc::SOCKET;
#[cfg(unix)]    pub type sock_t = super::file::fd_t;

fn addr_to_sockaddr(addr: ip::SocketAddr) -> (libc::sockaddr_storage, uint) {
    unsafe {
        let storage: libc::sockaddr_storage = intrinsics::init();
        let len = match addr.ip {
            ip::Ipv4Addr(a, b, c, d) => {
                let storage: *mut libc::sockaddr_in = cast::transmute(&storage);
                (*storage).sin_family = libc::AF_INET as libc::sa_family_t;
                (*storage).sin_port = htons(addr.port);
                (*storage).sin_addr.s_addr = (d as u32 << 24) |
                                             (c as u32 << 16) |
                                             (b as u32 <<  8) |
                                             (a as u32 <<  0);
                mem::size_of::<libc::sockaddr_in>()
            }
            ip::Ipv6Addr(a, b, c, d, e, f, g, h) => {
                let storage: *mut libc::sockaddr_in6 = cast::transmute(&storage);
                (*storage).sin6_family = libc::AF_INET6 as libc::sa_family_t;
                (*storage).sin6_port = htons(addr.port);
                (*storage).sin6_addr.s6_addr[0] = htons(a);
                (*storage).sin6_addr.s6_addr[1] = htons(b);
                (*storage).sin6_addr.s6_addr[2] = htons(c);
                (*storage).sin6_addr.s6_addr[3] = htons(d);
                (*storage).sin6_addr.s6_addr[4] = htons(e);
                (*storage).sin6_addr.s6_addr[5] = htons(f);
                (*storage).sin6_addr.s6_addr[6] = htons(g);
                (*storage).sin6_addr.s6_addr[7] = htons(h);
                mem::size_of::<libc::sockaddr_in6>()
            }
        };
        return (storage, len);
    }
}

fn socket(addr: ip::SocketAddr) -> IoResult<FileDesc> {
    unsafe {
        let fam = match addr.ip {
            ip::Ipv4Addr(..) => libc::AF_INET,
            ip::Ipv6Addr(..) => libc::AF_INET6,
        };
        match libc::socket(fam, libc::SOCK_STREAM, 0) {
            -1 => Err(super::last_error()),
            fd => Ok(FileDesc::new(fd as super::file::fd_t, CloseSocket))
        }
    }
}

fn sockname(fd: sock_t,
            f: extern "system" unsafe fn(sock_t, *mut libc::sockaddr,
                                         *mut libc::socklen_t) -> libc::c_int)
    -> IoResult<ip::SocketAddr>
{
    let mut storage: libc::sockaddr_storage = unsafe { intrinsics::init() };
    let mut len = mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
    unsafe {
        let storage = &mut storage as *mut libc::sockaddr_storage;
        let ret = f(fd,
                    storage as *mut libc::sockaddr,
                    &mut len as *mut libc::socklen_t);
        if ret != 0 {
            return Err(super::last_error())
        }
    }
    match storage.ss_family as libc::c_int {
        libc::AF_INET => {
            assert!(len as uint >= mem::size_of::<libc::sockaddr_in>());
            let storage: &mut libc::sockaddr_in = unsafe {
                cast::transmute(&mut storage)
            };
            let addr = storage.sin_addr.s_addr as u32;
            let a = (addr >>  0) as u8;
            let b = (addr >>  8) as u8;
            let c = (addr >> 16) as u8;
            let d = (addr >> 24) as u8;
            Ok(ip::SocketAddr {
                ip: ip::Ipv4Addr(a, b, c, d),
                port: ntohs(storage.sin_port),
            })
        }
        libc::AF_INET6 => {
            assert!(len as uint >= mem::size_of::<libc::sockaddr_in6>());
            let storage: &mut libc::sockaddr_in6 = unsafe {
                cast::transmute(&mut storage)
            };
            let a = ntohs(storage.sin6_addr.s6_addr[0]);
            let b = ntohs(storage.sin6_addr.s6_addr[1]);
            let c = ntohs(storage.sin6_addr.s6_addr[2]);
            let d = ntohs(storage.sin6_addr.s6_addr[3]);
            let e = ntohs(storage.sin6_addr.s6_addr[4]);
            let f = ntohs(storage.sin6_addr.s6_addr[5]);
            let g = ntohs(storage.sin6_addr.s6_addr[6]);
            let h = ntohs(storage.sin6_addr.s6_addr[7]);
            Ok(ip::SocketAddr {
                ip: ip::Ipv6Addr(a, b, c, d, e, f, g, h),
                port: ntohs(storage.sin6_port),
            })
        }
        _ => {
            Err(io::standard_error(io::OtherIoError))
        }
    }
}

impl TcpStream {
    pub fn connect(addr: ip::SocketAddr) -> IoResult<TcpStream> {
        unsafe {
            socket(addr).and_then(|fd| {
                let (addr, len) = addr_to_sockaddr(addr);
                let addrp = &addr as *libc::sockaddr_storage;
                match libc::connect(fd.fd() as sock_t, addrp as *libc::sockaddr,
                                    len as libc::socklen_t) {
                    -1 => Err(super::last_error()),
                    _ => Ok(TcpStream { fd: fd }),
                }
            })
        }
    }

    pub fn fd(&self) -> super::file::fd_t {
        self.fd.fd()
    }

    fn set_nodelay(&mut self, nodelay: bool) -> IoResult<()> {
        unsafe {
            let on = nodelay as libc::c_int;
            let on = &on as *libc::c_int;
            super::mkerr_libc(libc::setsockopt(self.fd.fd() as sock_t,
                                               libc::IPPROTO_TCP,
                                               libc::TCP_NODELAY,
                                               on as *libc::c_void,
                                               mem::size_of::<libc::c_void>()
                                                    as libc::socklen_t))
        }
    }

    fn set_keepalive(&mut self, seconds: Option<uint>) -> IoResult<()> {
        unsafe {
            let on = seconds.is_some() as libc::c_int;
            let on = &on as *libc::c_int;
            let ret = libc::setsockopt(self.fd.fd() as sock_t,
                                       libc::SOL_SOCKET,
                                       libc::SO_KEEPALIVE,
                                       on as *libc::c_void,
                                       mem::size_of::<libc::c_void>()
                                            as libc::socklen_t);
            if ret != 0 { return Err(super::last_error()) }

            match seconds {
                Some(n) => self.set_tcp_keepalive(n),
                None => Ok(())
            }
        }
    }

    #[cfg(target_os = "macos")]
    unsafe fn set_tcp_keepalive(&mut self, seconds: uint) -> IoResult<()> {
        let delay = seconds as libc::c_uint;
        let delay = &delay as *libc::c_uint;
        let ret = libc::setsockopt(self.fd.fd() as sock_t,
                                   libc::IPPROTO_TCP,
                                   libc::TCP_KEEPALIVE,
                                   delay as *libc::c_void,
                                   mem::size_of::<libc::c_uint>()
                                        as libc::socklen_t);
        super::mkerr_libc(ret)
    }
    #[cfg(target_os = "freebsd")]
    unsafe fn set_tcp_keepalive(&mut self, seconds: uint) -> IoResult<()> {
        let delay = seconds as libc::c_uint;
        let delay = &delay as *libc::c_uint;
        let ret = libc::setsockopt(self.fd.fd() as sock_t,
                                   libc::IPPROTO_TCP,
                                   libc::TCP_KEEPIDLE,
                                   delay as *libc::c_void,
                                   mem::size_of::<libc::c_uint>()
                                        as libc::socklen_t);
        super::mkerr_libc(ret)
    }
    #[cfg(not(target_os = "macos"), not(target_os = "freebsd"))]
    unsafe fn set_tcp_keepalive(&mut self, _seconds: uint) -> IoResult<()> {
        Ok(())
    }
}

impl rtio::RtioTcpStream for TcpStream {
    fn read(&mut self, buf: &mut [u8]) -> IoResult<uint> {
        self.fd.inner_read(buf)
    }
    fn write(&mut self, buf: &[u8]) -> IoResult<()> {
        self.fd.inner_write(buf)
    }
    fn peer_name(&mut self) -> IoResult<ip::SocketAddr> {
        sockname(self.fd() as sock_t, libc::getpeername)
    }
    fn control_congestion(&mut self) -> IoResult<()> {
        self.set_nodelay(false)
    }
    fn nodelay(&mut self) -> IoResult<()> {
        self.set_nodelay(true)
    }
    fn keepalive(&mut self, delay_in_seconds: uint) -> IoResult<()> {
        self.set_keepalive(Some(delay_in_seconds))
    }
    fn letdie(&mut self) -> IoResult<()> {
        self.set_keepalive(None)
    }
}

impl rtio::RtioSocket for TcpStream {
    fn socket_name(&mut self) -> IoResult<ip::SocketAddr> {
        sockname(self.fd() as sock_t, libc::getsockname)
    }
}

pub struct TcpListener {
    priv fd: super::FileDesc,
}

impl TcpListener {
    pub fn bind(addr: ip::SocketAddr) -> IoResult<TcpListener> {
        unsafe {
            socket(addr).and_then(|fd| {
                let (addr, len) = addr_to_sockaddr(addr);
                let addrp = &addr as *libc::sockaddr_storage;
                match libc::bind(fd.fd() as sock_t, addrp as *libc::sockaddr,
                                 len as libc::socklen_t) {
                    -1 => Err(super::last_error()),
                    _ => Ok(TcpListener { fd: fd })
                }
            })
        }
    }

    pub fn fd(&self) -> super::file::fd_t {
        self.fd.fd()
    }

    pub fn native_listen(self, backlog: int) -> IoResult<TcpAcceptor> {
        match unsafe { libc::listen(self.fd() as sock_t, backlog as libc::c_int) } {
            -1 => Err(super::last_error()),
            _ => Ok(TcpAcceptor { fd: self.fd })
        }
    }
}

impl rtio::RtioTcpListener for TcpListener {
    fn listen(~self) -> IoResult<~rtio::RtioTcpAcceptor> {
        self.native_listen(128).map(|a| ~a as ~rtio::RtioTcpAcceptor)
    }
}

impl rtio::RtioSocket for TcpListener {
    fn socket_name(&mut self) -> IoResult<ip::SocketAddr> {
        sockname(self.fd() as sock_t, libc::getsockname)
    }
}

pub struct TcpAcceptor {
    priv fd: FileDesc,
}

impl TcpAcceptor {
    pub fn fd(&self) -> super::file::fd_t {
        self.fd.fd()
    }

    pub fn native_accept(&mut self) -> IoResult<TcpStream> {
        unsafe {
            let mut storage: libc::sockaddr_storage = intrinsics::init();
            let storagep = &mut storage as *mut libc::sockaddr_storage;
            let size = mem::size_of::<libc::sockaddr_storage>();
            let mut size = size as libc::socklen_t;
            match libc::accept(self.fd() as sock_t,
                               storagep as *mut libc::sockaddr,
                               &mut size as *mut libc::socklen_t) {
                -1 => Err(super::last_error()),
                fd => Ok(TcpStream {
                    fd: FileDesc::new(fd as super::file::fd_t, CloseSocket)
                })
            }
        }
    }
}

impl rtio::RtioSocket for TcpAcceptor {
    fn socket_name(&mut self) -> IoResult<ip::SocketAddr> {
        sockname(self.fd() as sock_t, libc::getsockname)
    }
}

impl rtio::RtioTcpAcceptor for TcpAcceptor {
    fn accept(&mut self) -> IoResult<~rtio::RtioTcpStream> {
        self.native_accept().map(|s| ~s as ~rtio::RtioTcpStream)
    }

    fn accept_simultaneously(&mut self) -> IoResult<()> { Ok(()) }
    fn dont_accept_simultaneously(&mut self) -> IoResult<()> { Ok(()) }
}
