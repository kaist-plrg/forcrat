use lazy_static::lazy_static;

use crate::{compile_util::Pass, formatter, ty_checker};

#[inline]
fn run_test<F: FnOnce(&str)>(s: &str, f: F) {
    let mut code = PREAMBLE.to_string();
    code.push_str(s);
    let v = super::Transformation.run_on_str(&code);
    let [(_, s)] = &v[..] else { panic!() };
    f(s.strip_prefix(FORMATTED_PREAMBLE.as_str()).unwrap());
    assert!(ty_checker::TyChecker.run_on_str(&s));
}

#[test]
fn test_fgetc() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {{
    fgetc(stream);
    return fgetc(stream);
}}",
        |s| {
            assert!(s.contains("Read"));
            assert!(s.contains("read_exact"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fgetc"));
        },
    );
}

const PREAMBLE: &str = r#"
#![feature(extern_types)]
use ::libc;
extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
    fn fgetc(__stream: *mut FILE) -> libc::c_int;
}
pub type size_t = libc::c_ulong;
pub type __off_t = libc::c_long;
pub type __off64_t = libc::c_long;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct _IO_FILE {
    pub _flags: libc::c_int,
    pub _IO_read_ptr: *mut libc::c_char,
    pub _IO_read_end: *mut libc::c_char,
    pub _IO_read_base: *mut libc::c_char,
    pub _IO_write_base: *mut libc::c_char,
    pub _IO_write_ptr: *mut libc::c_char,
    pub _IO_write_end: *mut libc::c_char,
    pub _IO_buf_base: *mut libc::c_char,
    pub _IO_buf_end: *mut libc::c_char,
    pub _IO_save_base: *mut libc::c_char,
    pub _IO_backup_base: *mut libc::c_char,
    pub _IO_save_end: *mut libc::c_char,
    pub _markers: *mut _IO_marker,
    pub _chain: *mut _IO_FILE,
    pub _fileno: libc::c_int,
    pub _flags2: libc::c_int,
    pub _old_offset: __off_t,
    pub _cur_column: libc::c_ushort,
    pub _vtable_offset: libc::c_schar,
    pub _shortbuf: [libc::c_char; 1],
    pub _lock: *mut libc::c_void,
    pub _offset: __off64_t,
    pub _codecvt: *mut _IO_codecvt,
    pub _wide_data: *mut _IO_wide_data,
    pub _freeres_list: *mut _IO_FILE,
    pub _freeres_buf: *mut libc::c_void,
    pub __pad5: size_t,
    pub _mode: libc::c_int,
    pub _unused2: [libc::c_char; 20],
}
pub type _IO_lock_t = ();
pub type FILE = _IO_FILE;"#;

lazy_static! {
    static ref FORMATTED_PREAMBLE: String = formatter::Formatter.run_on_str(PREAMBLE);
}
