use etrace::some_or;
use lazy_static::lazy_static;
use rustc_data_structures::fx::FxHashMap;
use rustc_index::Idx;
use rustc_middle::{query::IntoQueryParam, ty::TyCtxt};
use rustc_span::{def_id::DefId, Symbol};
use ApiKind::*;
use Origin::*;
use Permission::*;

use crate::compile_util::def_id_to_value_symbol;

#[inline]
pub fn symbol_api_kind(name: Symbol) -> Option<ApiKind> {
    API_MAP.get(normalize_api_name(name.as_str())).copied()
}

#[inline]
pub fn def_id_api_kind(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> Option<ApiKind> {
    symbol_api_kind(def_id_to_value_symbol(id, tcx)?)
}

#[inline]
pub fn is_symbol_api(name: Symbol) -> bool {
    API_MAP.contains_key(normalize_api_name(name.as_str()))
}

#[inline]
pub fn is_def_id_api(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    is_symbol_api(some_or!(def_id_to_value_symbol(id, tcx), return false))
}

#[inline]
pub fn normalize_api_name(name: &str) -> &str {
    if name == "__printf__" {
        return "printf";
    }
    let name = name.strip_suffix("_unlocked").unwrap_or(name);
    name.strip_prefix("rpl_").unwrap_or(name)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Permission {
    Read = 0,
    BufRead = 1,
    Write = 2,
    Seek = 3,
    AsRawFd = 4,
    Lock = 5,
    Close = 6,
}

impl Permission {
    pub const NUM: usize = 7;

    #[inline]
    pub fn full_name(self) -> &'static str {
        match self {
            Self::Read => "std::io::Read",
            Self::BufRead => "std::io::BufRead",
            Self::Write => "std::io::Write",
            Self::Seek => "std::io::Seek",
            Self::AsRawFd => "std::os::fd::AsRawFd",
            _ => panic!(),
        }
    }
}

impl Idx for Permission {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx >= Self::NUM {
            panic!()
        }
        unsafe { std::mem::transmute(idx as u8) }
    }

    #[inline]
    fn index(self) -> usize {
        self as _
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Origin {
    Stdin = 0,
    Stdout = 1,
    Stderr = 2,
    File = 3,
    PipeRead = 4,
    PipeWrite = 5,
    PipeDyn = 6,
    Buffer = 7,
}

impl Origin {
    pub const NUM: usize = 8;
}

impl Idx for Origin {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx >= Self::NUM {
            panic!()
        }
        unsafe { std::mem::transmute(idx as u8) }
    }

    #[inline]
    fn index(self) -> usize {
        self as _
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ApiKind {
    Open(Origin),
    PipeOpen,
    Operation(Option<Permission>),
    StdioOperation,
    NotIO,
    Unsupported,
}

impl ApiKind {
    #[inline]
    pub fn is_read(self) -> bool {
        matches!(self, Operation(Some(Read)))
    }

    #[inline]
    pub fn is_write(self) -> bool {
        matches!(self, Operation(Some(Write)))
    }

    #[inline]
    pub fn is_unsupported(self) -> bool {
        matches!(self, Unsupported)
    }
}

lazy_static! {
    pub static ref API_MAP: FxHashMap<&'static str, ApiKind> = API_LIST.iter().copied().collect();
}

pub static API_LIST: [(&str, ApiKind); 81] = [
    // stdio.h
    // Open (6)
    ("fopen", Open(File)),
    ("fdopen", Open(File)),
    ("tmpfile", Open(File)),
    ("popen", PipeOpen),
    ("fmemopen", Open(Buffer)),
    ("open_memstream", Open(Buffer)),
    // Close (2)
    ("fclose", Operation(Some(Close))),
    ("pclose", Operation(Some(Close))),
    // Read (10)
    ("fscanf", Operation(Some(BufRead))),
    ("vfscanf", Unsupported),
    ("getc", Operation(Some(Read))), // unlocked
    ("fgetc", Operation(Some(Read))),
    ("fgets", Operation(Some(BufRead))),
    ("fread", Operation(Some(Read))),
    ("ungetc", Unsupported),
    ("getline", Operation(Some(BufRead))),
    ("getdelim", Operation(Some(BufRead))),
    // Read stdin (5)
    ("scanf", StdioOperation),
    ("vscanf", StdioOperation),
    ("getchar", StdioOperation), // unlocked
    ("gets", StdioOperation),    // removed
    // Read string (2)
    // ("sscanf", NotIO),
    // ("vsscanf", NotIO),
    // Write (8)
    ("fprintf", Operation(Some(Write))),
    ("vfprintf", Unsupported),
    ("putc", Operation(Some(Write))), // unlocked
    ("fputc", Operation(Some(Write))),
    ("fputs", Operation(Some(Write))),
    ("fwrite", Operation(Some(Write))),
    ("fflush", Operation(Some(Write))),
    // Write stdout/stderr (6)
    ("printf", StdioOperation),
    ("vprintf", StdioOperation),
    ("putchar", StdioOperation), // unlocked
    ("puts", StdioOperation),
    ("perror", StdioOperation),
    // Write fd (2)
    ("dprintf", Unsupported),
    ("vdprintf", Unsupported),
    // Write string (4)
    // ("sprintf", NotIO),
    // ("vsprintf", NotIO),
    // ("snprintf", NotIO),
    // ("vsnprintf", NotIO),
    // Positioning (7)
    ("fseek", Operation(Some(Seek))),
    ("fseeko", Operation(Some(Seek))),
    ("ftell", Operation(Some(Seek))),
    ("ftello", Operation(Some(Seek))),
    ("rewind", Operation(Some(Seek))),
    ("fgetpos", Operation(Some(Seek))),
    ("fsetpos", Operation(Some(Seek))),
    // Error (3)
    ("clearerr", Operation(None)),
    ("feof", Operation(Some(Read))),
    ("ferror", Operation(None)),
    // Locking (3)
    ("flockfile", Operation(Some(Lock))),
    ("ftrylockfile", Operation(Some(Lock))),
    ("funlockfile", Operation(Some(Lock))),
    // Buffering (2)
    ("setvbuf", Unsupported),
    ("setbuf", Unsupported),
    // Other (2)
    ("freopen", Unsupported),
    ("fileno", Operation(Some(AsRawFd))),
    // File system (6)
    ("rename", NotIO),
    ("renameat", NotIO),
    ("remove", NotIO),
    ("tmpnam", NotIO),
    ("tempnam", NotIO), // removed
    ("ctermid", NotIO),
    // GNU libc
    ("__fpending", Unsupported),
    ("__freading", Unsupported),
    ("__fwriting", Unsupported),
    ("fpurge", Unsupported),
    // wchar.h
    // Open (1)
    ("open_wmemstream", Open(Buffer)),
    // Read (6)
    ("fwscanf", Operation(Some(BufRead))),
    ("vfwscanf", Unsupported),
    ("getwc", Operation(Some(Read))),
    ("fgetwc", Operation(Some(Read))),
    ("fgetws", Operation(Some(BufRead))),
    ("ungetwc", Unsupported),
    // Read stdin (3)
    ("wscanf", StdioOperation),
    ("vwscanf", StdioOperation),
    ("getwchar", StdioOperation),
    // Read string (2)
    // ("swscanf", NotIO),
    // ("vswscanf", NotIO),
    // Write (5)
    ("fwprintf", Operation(Some(Write))),
    ("vfwprintf", Unsupported),
    ("putwc", Operation(Some(Write))),
    ("fputwc", Operation(Some(Write))),
    ("fputws", Operation(Some(Write))),
    // Write stdout/stderr (3)
    ("wprintf", StdioOperation),
    ("vwprintf", StdioOperation),
    ("putwchar", StdioOperation),
    // Write string (2)
    // ("swprintf", NotIO),
    // ("vswprintf", NotIO),
    // Orientation (1)
    ("fwide", Unsupported),
];
