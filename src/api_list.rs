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
    API_SET.get(normalize_api_name(name.as_str())).copied()
}

#[inline]
pub fn def_id_api_kind(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> Option<ApiKind> {
    symbol_api_kind(def_id_to_value_symbol(id, tcx)?)
}

#[inline]
pub fn is_symbol_api(name: Symbol) -> bool {
    API_SET.contains_key(normalize_api_name(name.as_str()))
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
    Write = 1,
    Seek = 2,
    Close = 3,
}

impl Idx for Permission {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx > 3 {
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
    Pipe = 4,
    Buffer = 5,
}

impl Idx for Origin {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx > 5 {
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
}

lazy_static! {
    pub static ref API_SET: FxHashMap<&'static str, ApiKind> = API_LIST.iter().copied().collect();
}

pub static API_LIST: [(&str, ApiKind); 87] = [
    // stdio.h
    // Open (6)
    ("fopen", Open(File)),
    ("fdopen", Open(File)),
    ("tmpfile", Open(File)),
    ("popen", Open(Pipe)),
    ("fmemopen", Open(Buffer)),
    ("open_memstream", Open(Buffer)),
    // Close (2)
    ("fclose", Operation(Some(Close))),
    ("pclose", Operation(Some(Close))),
    // Read (10)
    ("fscanf", Operation(Some(Read))),
    ("vfscanf", Operation(Some(Read))),
    ("getc", Operation(Some(Read))), // unlocked
    ("fgetc", Operation(Some(Read))),
    ("fgets", Operation(Some(Read))),
    ("fread", Operation(Some(Read))),
    ("ungetc", Unsupported),
    ("getline", Operation(Some(Read))),
    ("getdelim", Operation(Some(Read))),
    // Read stdin (5)
    ("scanf", StdioOperation),
    ("vscanf", StdioOperation),
    ("getchar", StdioOperation), // unlocked
    ("gets", StdioOperation),    // removed
    // Read string (2)
    ("sscanf", NotIO),
    ("vsscanf", NotIO),
    // Write (8)
    ("fprintf", Operation(Some(Write))),
    ("vfprintf", Operation(Some(Write))),
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
    ("sprintf", NotIO),
    ("vsprintf", NotIO),
    ("snprintf", NotIO),
    ("vsnprintf", NotIO),
    // Positioning (7)
    ("fseek", Operation(Some(Seek))),
    ("fseeko", Operation(Some(Seek))),
    ("ftell", Operation(Some(Seek))),
    ("ftello", Operation(Some(Seek))),
    ("rewind", Operation(Some(Seek))),
    ("fgetpos", Operation(Some(Seek))),
    ("fsetpos", Operation(Some(Seek))),
    // Error (3)
    ("clearerr", Unsupported),
    ("feof", Unsupported),
    ("ferror", Unsupported),
    // Locking (3)
    ("flockfile", Operation(None)),
    ("ftrylockfile", Operation(None)),
    ("funlockfile", Operation(None)),
    // Buffering (2)
    ("setvbuf", Unsupported),
    ("setbuf", Unsupported),
    // Other (2)
    ("freopen", Unsupported),
    ("fileno", Unsupported),
    // File system (6)
    ("rename", NotIO),
    ("renameat", NotIO),
    ("remove", NotIO),
    ("tmpnam", NotIO),
    ("tempnam", NotIO), // removed
    ("ctermid", NotIO),
    // wchar.h
    // Open (1)
    ("open_wmemstream", Open(Buffer)),
    // Read (6)
    ("fwscanf", Operation(Some(Read))),
    ("vfwscanf", Operation(Some(Read))),
    ("getwc", Operation(Some(Read))),
    ("fgetwc", Operation(Some(Read))),
    ("fgetws", Operation(Some(Read))),
    ("ungetwc", Unsupported),
    // Read stdin (3)
    ("wscanf", StdioOperation),
    ("vwscanf", StdioOperation),
    ("getwchar", StdioOperation),
    // Read string (2)
    ("swscanf", NotIO),
    ("vswscanf", NotIO),
    // Write (5)
    ("fwprintf", Operation(Some(Write))),
    ("vfwprintf", Operation(Some(Write))),
    ("putwc", Operation(Some(Write))),
    ("fputwc", Operation(Some(Write))),
    ("fputws", Operation(Some(Write))),
    // Write stdout/stderr (3)
    ("wprintf", StdioOperation),
    ("vwprintf", StdioOperation),
    ("putwchar", StdioOperation),
    // Write string (2)
    ("swprintf", NotIO),
    ("vswprintf", NotIO),
    // Orientation (1)
    ("fwide", Unsupported),
];
