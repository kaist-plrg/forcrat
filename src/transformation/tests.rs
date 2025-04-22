use lazy_static::lazy_static;

use crate::{compile_util::Pass, formatter, ty_checker};

fn run_test(s: &str, includes: &[&str], excludes: &[&str]) {
    let mut code = PREAMBLE.to_string();
    code.push_str(s);
    let res = super::Transformation.run_on_str(&code);
    let [(_, s)] = &res.files[..] else { panic!() };
    let stripped = s.strip_prefix(FORMATTED_PREAMBLE.as_str()).unwrap();
    let res = ty_checker::TyChecker.try_on_str(&s).expect(&stripped);
    assert!(res, "{}", stripped);
    for s in includes {
        assert!(stripped.contains(s), "{}\nmust contain {}", stripped, s);
    }
    for s in excludes {
        assert!(
            !stripped.contains(s),
            "{}\nmust not contain {}",
            stripped,
            s
        );
    }
}

#[test]
fn test_stdin() {
    run_test(
        "unsafe fn f() { fgetc(stdin); }",
        &["read_exact", "std::io::stdin"],
        &["fgetc"],
    );
}

#[test]
fn test_stdout() {
    run_test(
        "unsafe fn f() { fputc('a' as i32, stdout); }",
        &["write_all", "std::io::stdout"],
        &["fputc"],
    );
}

#[test]
fn test_stderr() {
    run_test(
        "unsafe fn f() { fputc('a' as i32, stderr); }",
        &["write_all", "std::io::stderr"],
        &["fputc"],
    );
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
        &["Read", "open", "read_exact", "drop"],
        &["FILE", "fopen", "fgetc", "fclose"],
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
        &[
            "BufRead",
            "open",
            "fill_buf",
            "available",
            "consume",
            "drop",
        ],
        &["FILE", "fopen", "fgets", "fclose"],
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
        &["Write", "create", "write_all", "drop"],
        &["FILE", "fopen", "fputc", "fclose"],
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
        &["Seek", "open", "rewind", "drop"],
        &["FILE", "fopen", "fclose"],
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
        &["Read", "Command", "ChildStdout", "stdout", "drop"],
        &["FILE", "popen", "pclose"],
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
        &["Write", "Command", "ChildStdin", "stdin", "drop"],
        &["FILE", "popen", "pclose"],
    );
}

#[test]
fn test_fscanf_numbers() {
    run_test(
        r#"
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    let mut a: libc::c_int = 0;
    let mut b: libc::c_short = 0;
    let mut c: libc::c_long = 0;
    let mut d: libc::c_uint = 0;
    let mut e: libc::c_ushort = 0;
    let mut f_0: libc::c_ulong = 0;
    let mut g: libc::c_float = 0.;
    let mut h: libc::c_double = 0.;
    return fscanf(
        stream,
        b"%d %hd %ld %u %hu %lu %g %lg\0" as *const u8 as *const libc::c_char,
        &mut a as *mut libc::c_int,
        &mut b as *mut libc::c_short,
        &mut c as *mut libc::c_long,
        &mut d as *mut libc::c_uint,
        &mut e as *mut libc::c_ushort,
        &mut f_0 as *mut libc::c_ulong,
        &mut g as *mut libc::c_float,
        &mut h as *mut libc::c_double,
    );
}"#,
        &["BufRead", "fill_buf", "available", "consume", "parse"],
        &["FILE", "fscanf"],
    );
}

#[test]
fn test_fscanf_strings() {
    run_test(
        r#"
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    let mut buf1: [libc::c_char; 1024] = [0; 1024];
    let mut buf2: [libc::c_char; 1024] = [0; 1024];
    return fscanf(
        stream,
        b"%*s %s %10s\0" as *const u8 as *const libc::c_char,
        buf1.as_mut_ptr(),
        buf2.as_mut_ptr(),
    );
}"#,
        &[
            "BufRead",
            "fill_buf",
            "available",
            "consume",
            "copy_from_slice",
        ],
        &["FILE", "fscanf"],
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
        &["Read", "read_exact"],
        &["FILE", "fgetc"],
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
        &["Read", "read_exact"],
        &["FILE", "getc"],
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
        &["Read", "read_exact"],
        &["getchar"],
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
        &["BufRead", "fill_buf", "available", "consume"],
        &["FILE", "fgets"],
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
        &["BufRead", "fill_buf", "available", "consume", "lock"],
        &["FILE", "fgets"],
    );
}

#[test]
fn test_fread() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) {
    let mut buf1: [libc::c_char; 16] = [0; 16];
    let mut buf2: [libc::c_char; 16] = [0; 16];
    fread(
        buf1.as_mut_ptr() as *mut libc::c_void,
        1 as libc::c_int as libc::c_ulong,
        16 as libc::c_int as libc::c_ulong,
        stream,
    );
    fread(
        buf2.as_mut_ptr() as *mut libc::c_void,
        1 as libc::c_int as libc::c_ulong,
        16 as libc::c_int as libc::c_ulong,
        stream,
    );
}",
        &["Read", "read_exact"],
        &["FILE", "fread"],
    );
}

#[test]
fn test_fread_stdin() {
    run_test(
        "
unsafe fn f() {
    let mut buf1: [libc::c_char; 16] = [0; 16];
    let mut buf2: [libc::c_char; 16] = [0; 16];
    fread(
        buf1.as_mut_ptr() as *mut libc::c_void,
        1 as libc::c_int as libc::c_ulong,
        16 as libc::c_int as libc::c_ulong,
        stdin,
    );
    fread(
        buf2.as_mut_ptr() as *mut libc::c_void,
        1 as libc::c_int as libc::c_ulong,
        16 as libc::c_int as libc::c_ulong,
        stdin,
    );
}",
        &["Read", "read_exact"],
        &["fread"],
    );
}

#[test]
fn test_fprintf() {
    run_test(
        r#"
unsafe fn f(mut stream: *mut FILE) {
    fprintf(stream, b"%d\0" as *const u8 as *const libc::c_char, 0 as libc::c_int);
}"#,
        &["write!", "i32"],
        &["fprintf", "%d"],
    );
}

#[test]
fn test_printf_static() {
    run_test(
        r#"
static mut fmt1: [libc::c_char; 4] = unsafe {
    *::std::mem::transmute::<&[u8; 4], &[libc::c_char; 4]>(b"%d\n\0")
};
static mut fmt2: *const libc::c_char = b"%d\n\0" as *const u8 as *const libc::c_char;
unsafe fn f() {
    printf(fmt1.as_ptr(), 1 as libc::c_int);
    printf(fmt2, 1 as libc::c_int);
}"#,
        &["write!"],
        &["printf"],
    );
}

#[test]
fn test_wprintf() {
    run_test(
        r#"
unsafe fn f() {
    let mut s: *const wchar_t = (*::std::mem::transmute::<
        &[u8; 12],
        &[libc::c_int; 3],
    >(b"H\xC5\0\0U\xB1\0\0\0\0\0\0"))
        .as_ptr();
    wprintf(
        (*::std::mem::transmute::<
            &[u8; 20],
            &[libc::c_int; 5],
        >(b"%\0\0\0l\0\0\0s\0\0\0\n\0\0\0\0\0\0\0"))
            .as_ptr(),
        s,
    );
}"#,
        &["write!"],
        &["wprintf"],
    );
}

#[test]
fn test_fprintf_unknown() {
    run_test(
        r#"
static mut s1: *const libc::c_char = b"%d\0" as *const u8 as *const libc::c_char;
unsafe fn f(mut s2: *const libc::c_char) {
    fprintf(stdout, s1, 0 as libc::c_int);
    fprintf(stderr, s2, 0 as libc::c_int);
}"#,
        &["write!", "fprintf", "stderr"],
        &[],
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
        &["Write", "write_all"],
        &["FILE", "fputc"],
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
        &["Write", "write_all"],
        &["FILE", "putc"],
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
        &["write_all"],
        &["putchar"],
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
        &["Write", "write_all"],
        &["FILE", "fputs"],
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
        &["write_all"],
        &["puts"],
    );
}

#[test]
fn test_fwrite() {
    run_test(
        r#"
unsafe fn f(mut stream: *mut FILE) {
    fwrite(
        b"a\0" as *const u8 as *const libc::c_char as *const libc::c_void,
        1 as libc::c_int as libc::c_ulong,
        1 as libc::c_int as libc::c_ulong,
        stream,
    );
    fwrite(
        b"b\0" as *const u8 as *const libc::c_char as *const libc::c_void,
        1 as libc::c_int as libc::c_ulong,
        1 as libc::c_int as libc::c_ulong,
        stream,
    );
}"#,
        &["Write", "write_all"],
        &["FILE", "fwrite"],
    );
}

#[test]
fn test_fwrite_stdout() {
    run_test(
        r#"
unsafe fn f() {
    fwrite(
        b"a\0" as *const u8 as *const libc::c_char as *const libc::c_void,
        1 as libc::c_int as libc::c_ulong,
        1 as libc::c_int as libc::c_ulong,
        stdout,
    );
    fwrite(
        b"b\0" as *const u8 as *const libc::c_char as *const libc::c_void,
        1 as libc::c_int as libc::c_ulong,
        1 as libc::c_int as libc::c_ulong,
        stdout,
    );
}"#,
        &["Write", "write_all"],
        &["fwrite"],
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
        &["Write", "flush"],
        &["FILE", "fflush"],
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
        &["Seek", "stream_position"],
        &["FILE", "ftell"],
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
        &["Seek", "stream_position"],
        &["FILE", "ftello"],
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
        &["Seek", "rewind"],
        &["FILE"],
    );
}

#[test]
fn test_fileno() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) -> libc::c_int {
    fileno(stream);
    return fileno(stream);
}",
        &["AsRawFd", "as_raw_fd"],
        &["FILE", "fileno"],
    );
}

#[test]
fn test_fileno_call() {
    run_test(
        r#"
unsafe fn g(mut stream: *mut FILE) {
    fileno(stream);
}
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    g(stream);
    fclose(stream);
}"#,
        &["AsRawFd", "as_raw_fd"],
        &["FILE", "fileno"],
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
        &["None", "is_none"],
        &["0 as", "is_null"],
    );
}

#[test]
fn test_second_arg() {
    run_test(
        "
unsafe fn f(mut c: libc::c_int, mut stream: *mut FILE) {
    fputc(c, stream);
}",
        &["Write", "write_all"],
        &["FILE", "fputc"],
    );
}

#[test]
fn test_file_to_void() {
    run_test(
        "
unsafe fn f(mut stream: *mut FILE) {
    let mut p: *mut libc::c_void = stream as *mut libc::c_void;
    fputc('a' as i32, stream);
    putchar('a' as i32);
}",
        &["Write", "write_all", "FILE", "fputc"],
        &[],
    );
}

#[test]
fn test_void_to_file() {
    run_test(
        "
unsafe fn f(mut p: *mut libc::c_void) {
    let mut stream: *mut FILE = p as *mut FILE;
    fputc('a' as i32, stream);
    putchar('a' as i32);
}",
        &["Write", "write_all", "FILE", "fputc"],
        &[],
    );
}

#[test]
fn test_void_open_1() {
    run_test(
        r#"
unsafe fn g(mut p: *mut libc::c_void) {}
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"w\0" as *const u8 as *const libc::c_char,
    );
    g(stream as *mut libc::c_void);
    fputc('a' as i32, stream);
    putchar('a' as i32);
    fclose(stream);
}"#,
        &["Write", "write_all", "FILE", "fputc"],
        &[],
    );
}

#[test]
fn test_void_open_2() {
    run_test(
        r#"
unsafe fn g(mut p: *mut libc::c_void) {}
unsafe fn f() {
    let mut stream: *mut FILE = 0 as *mut FILE;
    g(stream as *mut libc::c_void);
    stream = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"w\0" as *const u8 as *const libc::c_char,
    );
    fputc('a' as i32, stream);
    putchar('a' as i32);
    fclose(stream);
}"#,
        &["Write", "write_all", "FILE", "fputc"],
        &[],
    );
}

#[test]
fn test_void_is_null() {
    run_test(
        r#"
unsafe fn f(mut p: *mut libc::c_void) {
    let mut stream: *mut FILE = p as *mut FILE;
    if stream.is_null() {
        return;
    }
    fputc('a' as i32, stream);
    putchar('a' as i32);
}"#,
        &["Write", "write_all", "FILE", "fputc"],
        &[],
    );
}

#[test]
fn test_static_void() {
    run_test(
        r#"
static mut stream: *mut FILE = 0 as *const FILE as *mut FILE;
unsafe fn f(mut p: *mut libc::c_void) {
    stream = p as *mut FILE;
    fputc('a' as i32, stream);
    putchar('a' as i32);
}"#,
        &["Write", "write_all", "FILE", "fputc"],
        &[],
    );
}

#[test]
fn test_bin_op() {
    run_test(
        r#"
unsafe fn f(mut stream: *mut FILE) {
    if stream == stdout {
        getchar();
        return;
    }
    fputc('a' as i32, stream);
}"#,
        &["Read", "read_exact", "FILE", "fputc"],
        &[],
    );
}

#[test]
fn test_field() {
    run_test(
        r#"
#[derive(Copy, Clone)]
#[repr(C)]
struct s {
    pub f: *mut FILE,
}
unsafe fn f() {
    let mut s: s = s { f: 0 as *mut FILE };
    s
        .f = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    fgetc(s.f);
    fgetc(s.f);
    fclose(s.f);
}"#,
        &["File", "open", "Read", "read_exact", "drop"],
        &["FILE", "fopen", "fgetc", "fclose"],
    );
}

#[test]
fn test_field_borrowed() {
    run_test(
        r#"
#[derive(Copy, Clone)]
#[repr(C)]
struct s {
    pub f: *mut FILE,
}
unsafe fn g(mut s: *mut s) {
    fgetc((*s).f);
    fgetc((*s).f);
}
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    let mut s: s = s { f: 0 as *mut FILE };
    s.f = stream;
    g(&mut s);
    g(&mut s);
    fclose(stream);
}"#,
        &["File", "open", "Read", "read_exact", "drop"],
        &["FILE", "fopen", "fgetc", "fclose"],
    );
}

#[test]
fn test_field_borrowed_init() {
    run_test(
        r#"
#[derive(Copy, Clone)]
#[repr(C)]
struct s {
    pub f: *mut FILE,
}
unsafe fn g(mut s: *mut s) {
    fgetc((*s).f);
    fgetc((*s).f);
}
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    let mut s: s = {
        let mut init = s { f: stream };
        init
    };
    g(&mut s);
    g(&mut s);
    fclose(stream);
}"#,
        &["File", "open", "Read", "read_exact", "drop"],
        &["FILE", "fopen", "fgetc", "fclose"],
    );
}

#[test]
fn test_nested_calls() {
    run_test(
        r#"
unsafe fn g(mut stream: *mut FILE) {
    fputc('a' as i32, stream);
    fputc('a' as i32, stream);
}
unsafe fn f(mut stream: *mut FILE) {
    g(stream);
    g(stream);
}"#,
        &["Write", "write_all"],
        &["FILE", "fputc"],
    );
}

#[test]
fn test_std_arg() {
    run_test(
        r#"
unsafe fn g(mut stream: *mut FILE) {
    fputc('a' as i32, stream);
    fputc('a' as i32, stream);
}
unsafe fn f() {
    g(stdout);
    g(stdout);
}"#,
        &["Write", "write_all", "std::io::stdout"],
        &["FILE", "fputc"],
    );
}

#[test]
fn test_indicators() {
    run_test(
        r#"
unsafe fn f() -> libc::c_int {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    fgetc(stream);
    if ferror(stream) != 0 {
        clearerr(stream);
        fclose(stream);
        return 0 as libc::c_int;
    } else if feof(stream) != 0 {
        clearerr(stream);
        fclose(stream);
        return 1 as libc::c_int;
    } else {
        fclose(stream);
        return 2 as libc::c_int
    };
}"#,
        &["Read", "read_exact", "std::io::ErrorKind"],
        &["FILE", "fgetc", "ferror", "feof", "clearerr"],
    );
}

#[test]
fn test_static() {
    run_test(
        r#"
static mut stream: *mut FILE = 0 as *const FILE as *mut FILE;
unsafe fn f() {
    stream = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"r\0" as *const u8 as *const libc::c_char,
    );
    fgetc(stream);
    fgetc(stream);
    fclose(stream);
}"#,
        &["Read", "read_exact", "drop"],
        &["FILE", "fgetc", "fclose"],
    );
}

#[test]
fn test_read_write() {
    run_test(
        r#"
unsafe fn f() {
    let mut stream: *mut FILE = fopen(
        b"a\0" as *const u8 as *const libc::c_char,
        b"w+\0" as *const u8 as *const libc::c_char,
    );
    let mut c: libc::c_int = fgetc(stream);
    fputc(c, stream);
    fclose(stream);
}"#,
        &["File", "Read", "read_exact", "Write", "write_all", "drop"],
        &["FILE", "fgetc", "fputc", "fclose"],
    );
}

#[test]
fn test_read_box() {
    run_test(
        r#"
unsafe fn f(mut x: libc::c_int) {
    let mut stream: *mut FILE = 0 as *mut FILE;
    if x != 0 {
        stream = fopen(
            b"a\0" as *const u8 as *const libc::c_char,
            b"r\0" as *const u8 as *const libc::c_char,
        );
    } else {
        stream = popen(
            b"ls\0" as *const u8 as *const libc::c_char,
            b"r\0" as *const u8 as *const libc::c_char,
        );
    }
    fgetc(stream);
    fgetc(stream);
    fclose(stream);
}"#,
        &["Box", "Read", "read_exact", "drop"],
        &["FILE", "fopen", "popen", "fgetc", "fclose"],
    );
}

#[test]
fn test_fopen_non_lit_mode() {
    run_test(
        r#"
unsafe fn f(mut mode: *const libc::c_char) {
    let mut stream: *mut FILE = fopen(b"a\0" as *const u8 as *const libc::c_char, mode);
    fgetc(stream);
    fgetc(stream);
    fclose(stream);
}"#,
        &["Read", "open", "read_exact", "drop"],
        &["FILE", "fopen", "fgetc", "fclose"],
    );
}

#[test]
fn test_tmpfile() {
    run_test(
        r#"
unsafe fn f() {
    let mut stream: *mut FILE = tmpfile();
    fputc('a' as i32, stream);
    fputc('a' as i32, stream);
    fclose(stream);
}"#,
        &["Write", "tempfile", "write_all", "drop"],
        &["FILE", "tmpfile", "fputc", "fclose"],
    );
}

#[test]
fn test_fdopen() {
    run_test(
        r#"
unsafe fn f() {
    let mut fd: libc::c_int = open(
        b"a\0" as *const u8 as *const libc::c_char,
        0 as libc::c_int,
    );
    let mut stream: *mut FILE = fdopen(fd, b"r\0" as *const u8 as *const libc::c_char);
    fgetc(stream);
    fgetc(stream);
    fclose(stream);
}"#,
        &["Read", "from_raw_fd", "read_exact", "drop"],
        &["FILE", "fdopen", "fgetc", "fclose"],
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
    fn open(__file: *const libc::c_char, __oflag: libc::c_int, _: ...) -> libc::c_int;
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
    fn wprintf(__format: *const wchar_t, _: ...) -> libc::c_int;
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
pub type fpos_t = __fpos_t;
pub type wchar_t = libc::c_int;"#;

lazy_static! {
    static ref FORMATTED_PREAMBLE: String = formatter::Formatter.run_on_str(PREAMBLE);
}
