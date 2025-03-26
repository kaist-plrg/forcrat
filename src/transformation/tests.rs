use lazy_static::lazy_static;

use crate::{compile_util::Pass, formatter, ty_checker};

fn run_test<F: FnOnce(&str)>(s: &str, f: F) {
    let mut code = PREAMBLE.to_string();
    code.push_str(s);
    let v = super::Transformation.run_on_str(&code);
    let [(_, s)] = &v[..] else { panic!() };
    let stripped = s.strip_prefix(FORMATTED_PREAMBLE.as_str()).unwrap();
    f(stripped);
    assert!(ty_checker::TyChecker.run_on_str(&s), "{}", stripped);
}

#[test]
fn test_stdin() {
    run_test("unsafe fn f() { fgetc(stdin); }", |s| {
        assert!(s.contains("read_exact"));
        assert!(s.contains("std::io::stdin"));
        assert!(!s.contains("fgetc"));
    });
}

#[test]
fn test_stdout() {
    run_test("unsafe fn f() { fputc('a' as i32, stdout); }", |s| {
        assert!(s.contains("write_all"));
        assert!(s.contains("std::io::stdout"));
        assert!(!s.contains("fputc"));
    });
}

#[test]
fn test_stderr() {
    run_test("unsafe fn f() { fputc('a' as i32, stderr); }", |s| {
        assert!(s.contains("write_all"));
        assert!(s.contains("std::io::stderr"));
        assert!(!s.contains("fputc"));
    });
}

#[test]
fn test_file_read() {
    run_test(
        r#"
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    fgetc(stream);
    fclose(stream);
}"#,
        |s| {
            assert!(s.contains("Read"));
            assert!(s.contains("open"));
            assert!(s.contains("read_exact"));
            assert!(s.contains("drop"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fopen"));
            assert!(!s.contains("fgetc"));
            assert!(!s.contains("fclose"));
        },
    );
}

#[test]
fn test_file_buf_read() {
    run_test(
        r#"
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    let mut buf: [libc::c_char; 1024] = [0; 1024];
    fgets(
        buf.as_mut_ptr(),
        ::std::mem::size_of::<[libc::c_char; 1024]>() as libc::c_ulong as libc::c_int,
        stream,
    );
    fclose(stream);
}"#,
        |s| {
            assert!(s.contains("BufRead"));
            assert!(s.contains("open"));
            assert!(s.contains("fill_buf"));
            assert!(s.contains("consume"));
            assert!(s.contains("drop"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fopen"));
            assert!(!s.contains("fgets"));
            assert!(!s.contains("fclose"));
        },
    );
}

#[test]
fn test_file_write() {
    run_test(
        r#"
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"w\0" as *const u8 as *const libc::c_char,
    );
    fputc('a' as i32, stream);
    fclose(stream);
}"#,
        |s| {
            assert!(s.contains("Write"));
            assert!(s.contains("create"));
            assert!(s.contains("write_all"));
            assert!(s.contains("drop"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fopen"));
            assert!(!s.contains("fputc"));
            assert!(!s.contains("fclose"));
        },
    );
}

#[test]
fn test_file_seek() {
    run_test(
        r#"
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    rewind(stream);
    fclose(stream);
}"#,
        |s| {
            assert!(s.contains("Seek"));
            assert!(s.contains("open"));
            assert!(s.contains("rewind"));
            assert!(s.contains("drop"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fopen"));
            assert!(!s.contains("fclose"));
        },
    );
}

#[test]
fn test_pipe_read() {
    run_test(
        r#"
unsafe fn f() {
    let mut f: *mut FILE = popen(
        b"ls\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    fgetc(f);
    pclose(f);
}"#,
        |s| {
            assert!(s.contains("Read"));
            assert!(s.contains("Command"));
            assert!(s.contains("ChildStdout"));
            assert!(s.contains("stdout"));
            assert!(s.contains("drop"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("popen"));
            assert!(!s.contains("pclose"));
        },
    );
}

#[test]
fn test_pipe_write() {
    run_test(
        r#"
unsafe fn f() {
    let mut f: *mut FILE = popen(
        b"/bin/bash\0" as *const u8 as *const libc::c_char,
        b"w\0" as *const u8 as *const libc::c_char,
    );
    fputs(b"echo hello\n\0" as *const u8 as *const libc::c_char, f);
    pclose(f);
}"#,
        |s| {
            assert!(s.contains("Write"));
            assert!(s.contains("Command"));
            assert!(s.contains("ChildStdin"));
            assert!(s.contains("stdin"));
            assert!(s.contains("drop"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("popen"));
            assert!(!s.contains("pclose"));
        },
    );
}

#[test]
fn test_fgetc() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    fgetc(stream);
    return fgetc(stream);
}",
        |s| {
            assert!(s.contains("Read"));
            assert!(s.contains("read_exact"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fgetc"));
        },
    );
}

#[test]
fn test_getc() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    getc(stream);
    return getc(stream);
}",
        |s| {
            assert!(s.contains("Read"));
            assert!(s.contains("read_exact"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("getc"));
        },
    );
}

#[test]
fn test_getchar() {
    run_test(
        "
unsafe fn f() -> libc::c_int {
    getchar();
    return getchar();
}",
        |s| {
            assert!(s.contains("read_exact"));
            assert!(!s.contains("getchar"));
        },
    );
}

#[test]
fn test_fgets() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) {
    let mut buf1: [libc::c_char; 1024] = [0; 1024];
    let mut buf2: [libc::c_char; 1024] = [0; 1024];
    fgets(
        buf1.as_mut_ptr(),
        ::std::mem::size_of::<[libc::c_char; 1024]>() as libc::c_ulong as libc::c_int,
        stream,
    );
    fgets(
        buf2.as_mut_ptr(),
        ::std::mem::size_of::<[libc::c_char; 1024]>() as libc::c_ulong as libc::c_int,
        stream,
    );
}",
        |s| {
            assert!(s.contains("BufRead"));
            assert!(s.contains("fill_buf"));
            assert!(s.contains("consume"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fgets"));
        },
    );
}

#[test]
fn test_fgets_stdin() {
    run_test(
        "
unsafe fn f() {
    let mut buf1: [libc::c_char; 1024] = [0; 1024];
    let mut buf2: [libc::c_char; 1024] = [0; 1024];
    fgets(
        buf1.as_mut_ptr(),
        ::std::mem::size_of::<[libc::c_char; 1024]>() as libc::c_ulong as libc::c_int,
        stdin,
    );
    fgets(
        buf2.as_mut_ptr(),
        ::std::mem::size_of::<[libc::c_char; 1024]>() as libc::c_ulong as libc::c_int,
        stdin,
    );
}",
        |s| {
            assert!(s.contains("BufRead"));
            assert!(s.contains("fill_buf"));
            assert!(s.contains("consume"));
            assert!(s.contains("lock"));
            assert!(!s.contains("fgets"));
        },
    );
}

#[test]
fn test_printf() {
    run_test(
        r#"
unsafe fn f(mut stream: *mut FILE) {
    fprintf(stream, b"%d\0" as *const u8 as *const libc::c_char, 0 as libc::c_int);
}"#,
        |s| {
            assert!(s.contains("write!"));
            assert!(s.contains("i32"));
            assert!(!s.contains("fprintf"));
            assert!(!s.contains("%d"));
        },
    );
}

#[test]
fn test_fputc() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    fputc('a' as i32, stream);
    return fputc('b' as i32, stream);
}",
        |s| {
            assert!(s.contains("Write"));
            assert!(s.contains("write_all"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fputc"));
        },
    );
}

#[test]
fn test_putc() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    putc('a' as i32, stream);
    return putc('b' as i32, stream);
}",
        |s| {
            assert!(s.contains("Write"));
            assert!(s.contains("write_all"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("putc"));
        },
    );
}

#[test]
fn test_putchar() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    putchar('a' as i32);
    return putchar('b' as i32);
}",
        |s| {
            assert!(s.contains("write_all"));
            assert!(!s.contains("putchar"));
        },
    );
}

#[test]
fn test_fputs() {
    run_test(
        r#"
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    fputs(b"a\0" as *const u8 as *const libc::c_char, stream);
    return fputs(b"b\0" as *const u8 as *const libc::c_char, stream);
}"#,
        |s| {
            assert!(s.contains("Write"));
            assert!(s.contains("write_all"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fputs"));
        },
    );
}

#[test]
fn test_puts() {
    run_test(
        r#"
unsafe fn f() -> libc::c_int {
    puts(b"a\0" as *const u8 as *const libc::c_char);
    return puts(b"b\0" as *const u8 as *const libc::c_char);
}"#,
        |s| {
            assert!(s.contains("write_all"));
            assert!(!s.contains("puts"));
        },
    );
}

#[test]
fn test_fflush() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    fflush(stream);
    return fflush(stream);
}",
        |s| {
            assert!(s.contains("Write"));
            assert!(s.contains("flush"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("fflush"));
        },
    );
}

#[test]
fn test_ftell() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_long {
    ftell(stream);
    return ftell(stream);
}",
        |s| {
            assert!(s.contains("Seek"));
            assert!(s.contains("stream_position"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("ftell"));
        },
    );
}

#[test]
fn test_ftello() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_long {
    ftello(stream);
    return ftello(stream);
}",
        |s| {
            assert!(s.contains("Seek"));
            assert!(s.contains("stream_position"));
            assert!(!s.contains("FILE"));
            assert!(!s.contains("ftello"));
        },
    );
}

#[test]
fn test_rewind() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) {
    rewind(stream);
    rewind(stream);
}",
        |s| {
            assert!(s.contains("Seek"));
            assert!(s.contains("rewind"));
            assert!(!s.contains("FILE"));
        },
    );
}

#[test]
fn test_null_arg() {
    run_test(
        "
unsafe fn g(mut f: *mut FILE) {
    if !f.is_null() {
        fputc('a' as i32, f);
    }
}
unsafe fn f() {
    g(0 as *mut FILE);
}",
        |s| {
            assert!(s.contains("None"));
            assert!(s.contains("is_none"));
            assert!(!s.contains("0"));
            assert!(!s.contains("is_null"));
        },
    );
}

const PREAMBLE: &str = r#"
#![feature(extern_types)]
#![feature(c_variadic)]
use ::libc;
extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
    static mut stdin: *mut FILE;
    static mut stdout: *mut FILE;
    static mut stderr: *mut FILE;
    fn remove(__filename: *const libc::c_char) -> libc::c_int;
    fn rename(__old: *const libc::c_char, __new: *const libc::c_char) -> libc::c_int;
    fn renameat(
        __oldfd: libc::c_int,
        __old: *const libc::c_char,
        __newfd: libc::c_int,
        __new: *const libc::c_char,
    ) -> libc::c_int;
    fn tmpfile() -> *mut FILE;
    fn tmpnam(__s: *mut libc::c_char) -> *mut libc::c_char;
    fn fclose(__stream: *mut FILE) -> libc::c_int;
    fn fflush(__stream: *mut FILE) -> libc::c_int;
    fn fopen(_: *const libc::c_char, _: *const libc::c_char) -> *mut FILE;
    fn freopen(
        __filename: *const libc::c_char,
        __modes: *const libc::c_char,
        __stream: *mut FILE,
    ) -> *mut FILE;
    fn fdopen(__fd: libc::c_int, __modes: *const libc::c_char) -> *mut FILE;
    fn fmemopen(
        __s: *mut libc::c_void,
        __len: size_t,
        __modes: *const libc::c_char,
    ) -> *mut FILE;
    fn open_memstream(
        __bufloc: *mut *mut libc::c_char,
        __sizeloc: *mut size_t,
    ) -> *mut FILE;
    fn setbuf(__stream: *mut FILE, __buf: *mut libc::c_char);
    fn setvbuf(
        __stream: *mut FILE,
        __buf: *mut libc::c_char,
        __modes: libc::c_int,
        __n: size_t,
    ) -> libc::c_int;
    fn fprintf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn printf(_: *const libc::c_char, _: ...) -> libc::c_int;
    fn sprintf(_: *mut libc::c_char, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn vfprintf(
        _: *mut FILE,
        _: *const libc::c_char,
        _: ::std::ffi::VaList,
    ) -> libc::c_int;
    fn vprintf(_: *const libc::c_char, _: ::std::ffi::VaList) -> libc::c_int;
    fn fscanf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn dprintf(__fd: libc::c_int, __fmt: *const libc::c_char, _: ...) -> libc::c_int;
    fn vsprintf(
        _: *mut libc::c_char,
        _: *const libc::c_char,
        _: ::std::ffi::VaList,
    ) -> libc::c_int;
    fn snprintf(
        _: *mut libc::c_char,
        _: libc::c_ulong,
        _: *const libc::c_char,
        _: ...
    ) -> libc::c_int;
    fn vsnprintf(
        _: *mut libc::c_char,
        _: libc::c_ulong,
        _: *const libc::c_char,
        _: ::std::ffi::VaList,
    ) -> libc::c_int;
    fn vdprintf(
        __fd: libc::c_int,
        __fmt: *const libc::c_char,
        __arg: ::std::ffi::VaList,
    ) -> libc::c_int;
    fn fseek(
        __stream: *mut FILE,
        __off: libc::c_long,
        __whence: libc::c_int,
    ) -> libc::c_int;
    fn scanf(_: *const libc::c_char, _: ...) -> libc::c_int;
    fn sscanf(_: *const libc::c_char, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn vfscanf(
        _: *mut FILE,
        _: *const libc::c_char,
        _: ::std::ffi::VaList,
    ) -> libc::c_int;
    fn vscanf(_: *const libc::c_char, _: ::std::ffi::VaList) -> libc::c_int;
    fn vsscanf(
        _: *const libc::c_char,
        _: *const libc::c_char,
        _: ::std::ffi::VaList,
    ) -> libc::c_int;
    fn fgetc(__stream: *mut FILE) -> libc::c_int;
    fn getc(__stream: *mut FILE) -> libc::c_int;
    fn getchar() -> libc::c_int;
    fn getc_unlocked(__stream: *mut FILE) -> libc::c_int;
    fn getchar_unlocked() -> libc::c_int;
    fn fputc(__c: libc::c_int, __stream: *mut FILE) -> libc::c_int;
    fn putc(__c: libc::c_int, __stream: *mut FILE) -> libc::c_int;
    fn putchar(__c: libc::c_int) -> libc::c_int;
    fn putc_unlocked(__c: libc::c_int, __stream: *mut FILE) -> libc::c_int;
    fn putchar_unlocked(__c: libc::c_int) -> libc::c_int;
    fn fgets(
        __s: *mut libc::c_char,
        __n: libc::c_int,
        __stream: *mut FILE,
    ) -> *mut libc::c_char;
    fn getdelim(
        __lineptr: *mut *mut libc::c_char,
        __n: *mut size_t,
        __delimiter: libc::c_int,
        __stream: *mut FILE,
    ) -> __ssize_t;
    fn getline(
        __lineptr: *mut *mut libc::c_char,
        __n: *mut size_t,
        __stream: *mut FILE,
    ) -> __ssize_t;
    fn fputs(__s: *const libc::c_char, __stream: *mut FILE) -> libc::c_int;
    fn puts(__s: *const libc::c_char) -> libc::c_int;
    fn ungetc(__c: libc::c_int, __stream: *mut FILE) -> libc::c_int;
    fn fread(
        _: *mut libc::c_void,
        _: libc::c_ulong,
        _: libc::c_ulong,
        _: *mut FILE,
    ) -> libc::c_ulong;
    fn fwrite(
        _: *const libc::c_void,
        _: libc::c_ulong,
        _: libc::c_ulong,
        _: *mut FILE,
    ) -> libc::c_ulong;
    fn ftell(__stream: *mut FILE) -> libc::c_long;
    fn rewind(__stream: *mut FILE);
    fn fseeko(__stream: *mut FILE, __off: __off_t, __whence: libc::c_int) -> libc::c_int;
    fn ftello(__stream: *mut FILE) -> __off_t;
    fn fgetpos(__stream: *mut FILE, __pos: *mut fpos_t) -> libc::c_int;
    fn fsetpos(__stream: *mut FILE, __pos: *const fpos_t) -> libc::c_int;
    fn clearerr(__stream: *mut FILE);
    fn feof(__stream: *mut FILE) -> libc::c_int;
    fn ferror(__stream: *mut FILE) -> libc::c_int;
    fn perror(__s: *const libc::c_char);
    fn fileno(__stream: *mut FILE) -> libc::c_int;
    fn popen(__command: *const libc::c_char, __modes: *const libc::c_char) -> *mut FILE;
    fn pclose(__stream: *mut FILE) -> libc::c_int;
    fn ctermid(__s: *mut libc::c_char) -> *mut libc::c_char;
    fn flockfile(__stream: *mut FILE);
    fn ftrylockfile(__stream: *mut FILE) -> libc::c_int;
    fn funlockfile(__stream: *mut FILE);
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct __va_list_tag {
    pub gp_offset: libc::c_uint,
    pub fp_offset: libc::c_uint,
    pub overflow_arg_area: *mut libc::c_void,
    pub reg_save_area: *mut libc::c_void,
}
pub type size_t = libc::c_ulong;
pub type __off_t = libc::c_long;
pub type __off64_t = libc::c_long;
pub type __ssize_t = libc::c_long;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct __mbstate_t {
    pub __count: libc::c_int,
    pub __value: C2RustUnnamed,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub union C2RustUnnamed {
    pub __wch: libc::c_uint,
    pub __wchb: [libc::c_char; 4],
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct _G_fpos_t {
    pub __pos: __off_t,
    pub __state: __mbstate_t,
}
pub type __fpos_t = _G_fpos_t;
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
pub type FILE = _IO_FILE;
pub type fpos_t = __fpos_t;"#;

lazy_static! {
    static ref FORMATTED_PREAMBLE: String = formatter::Formatter.run_on_str(PREAMBLE);
}
