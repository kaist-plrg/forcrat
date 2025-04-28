use std::ops::{Deref, DerefMut};

use etrace::some_or;
use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_index::Idx;
use typed_arena::Arena;

use crate::{
    api_list::{Origin, Permission},
    bit_set::BitSet8,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Pot<'a> {
    pub(super) permissions: BitSet8<Permission>,
    #[allow(unused)]
    pub(super) origins: BitSet8<Origin>,
    pub(super) ty: &'a StreamType<'a>,
}

pub(super) struct TypeArena<'a> {
    arena: &'a Arena<StreamType<'a>>,
}

impl<'a> TypeArena<'a> {
    #[inline]
    pub(super) fn new(arena: &'a Arena<StreamType<'a>>) -> Self {
        Self { arena }
    }

    #[inline]
    fn alloc(&self, ty: StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(ty)
    }

    #[inline]
    fn buf_writer(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::BufWriter(ty))
    }

    #[inline]
    fn buf_reader(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::BufReader(ty))
    }

    #[inline]
    fn option(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Option(ty))
    }

    #[inline]
    fn ptr(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Ptr(ty))
    }

    #[inline]
    fn box_(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Box(ty))
    }

    #[inline]
    fn manually_drop(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::ManuallyDrop(ty))
    }

    pub(super) fn make_ty(
        &self,
        permissions: BitSet8<Permission>,
        origins: BitSet8<Origin>,
        is_param: bool,
        is_union: bool,
    ) -> &'a StreamType<'a> {
        let ty = if is_param {
            let mut traits = BitSet8::new_empty();
            for p in permissions.iter() {
                traits.insert(some_or!(StreamTrait::from_permission(p), continue));
            }
            let ty = self.alloc(StreamType::Impl(TraitBound(traits)));
            self.option(ty)
        } else if origins.is_empty() {
            self.option(&FILE_TY)
        } else if origins.count() == 1 {
            let origin = origins.iter().next().unwrap();
            let ty = match origin {
                Origin::Stdin => &STDIN_TY,
                Origin::Stdout => &STDOUT_TY,
                Origin::Stderr => &STDERR_TY,
                Origin::File => {
                    if permissions.contains(Permission::Read)
                        && permissions.contains(Permission::Write)
                    {
                        &FILE_TY
                    } else if permissions.contains(Permission::Write) {
                        self.buf_writer(&FILE_TY)
                    } else if permissions.contains(Permission::Read)
                        || permissions.contains(Permission::BufRead)
                    {
                        self.buf_reader(&FILE_TY)
                    } else {
                        &FILE_TY
                    }
                }
                Origin::PipeRead => &CHILD_STDOUT_TY,
                Origin::PipeWrite => &CHILD_STDIN_TY,
                Origin::PipeDyn => todo!(),
                Origin::Buffer => todo!(),
            };
            if permissions.contains(Permission::Close)
                || origins.contains(Origin::Stdin)
                || origins.contains(Origin::Stdout)
                || origins.contains(Origin::Stderr)
            {
                self.option(ty)
            } else {
                self.ptr(ty)
            }
        } else {
            let mut traits = BitSet8::new_empty();
            for p in permissions.iter() {
                traits.insert(some_or!(StreamTrait::from_permission(p), continue));
            }
            if traits.is_empty() {
                traits.insert(StreamTrait::AsRawFd);
            }
            if traits.contains(StreamTrait::BufRead) {
                traits.remove(StreamTrait::Read);
            }
            let ty = self.alloc(StreamType::Dyn(TraitBound(traits)));
            let ty = if permissions.contains(Permission::Close) {
                self.box_(ty)
            } else {
                self.ptr(ty)
            };
            self.option(ty)
        };
        if is_union && !ty.is_copyable() {
            self.manually_drop(ty)
        } else {
            ty
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StreamType<'a> {
    File,
    Stdin,
    Stdout,
    Stderr,
    ChildStdin,
    ChildStdout,
    Option(&'a StreamType<'a>),
    BufWriter(&'a StreamType<'a>),
    BufReader(&'a StreamType<'a>),
    Ptr(&'a StreamType<'a>),
    Ref(&'a StreamType<'a>),
    Box(&'a StreamType<'a>),
    ManuallyDrop(&'a StreamType<'a>),
    Dyn(TraitBound),
    Impl(TraitBound),
}

pub(super) static STDIN_TY: StreamType<'static> = StreamType::Stdin;
pub(super) static STDOUT_TY: StreamType<'static> = StreamType::Stdout;
pub(super) static STDERR_TY: StreamType<'static> = StreamType::Stderr;
pub(super) static FILE_TY: StreamType<'static> = StreamType::File;
pub(super) static CHILD_STDIN_TY: StreamType<'static> = StreamType::ChildStdin;
pub(super) static CHILD_STDOUT_TY: StreamType<'static> = StreamType::ChildStdout;

impl std::fmt::Display for StreamType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::File => write!(f, "std::fs::File"),
            Self::Stdin => write!(f, "std::io::Stdin"),
            Self::Stdout => write!(f, "std::io::Stdout"),
            Self::Stderr => write!(f, "std::io::Stderr"),
            Self::ChildStdin => write!(f, "std::process::ChildStdin"),
            Self::ChildStdout => write!(f, "std::process::ChildStdout"),
            Self::Option(t) => write!(f, "Option<{}>", t),
            Self::BufWriter(t) => write!(f, "std::io::BufWriter<{}>", t),
            Self::BufReader(t) => write!(f, "std::io::BufReader<{}>", t),
            Self::Ptr(t) => write!(f, "*mut {}", t),
            Self::Ref(t) => write!(f, "&mut {}", t),
            Self::Box(t) => write!(f, "Box<{}>", t),
            Self::ManuallyDrop(t) => write!(f, "std::mem::ManuallyDrop<{}>", t),
            Self::Dyn(traits) => {
                if traits.count() == 1 {
                    write!(f, "dyn {}", traits)
                } else {
                    write!(f, "dyn crate::{}", traits.trait_name())
                }
            }
            Self::Impl(traits) => write!(f, "impl {}", traits),
        }
    }
}

impl StreamType<'_> {
    pub(super) fn is_copyable(self) -> bool {
        match self {
            Self::File
            | Self::Stdin
            | Self::Stdout
            | Self::Stderr
            | Self::ChildStdin
            | Self::ChildStdout
            | Self::BufWriter(_)
            | Self::BufReader(_)
            | Self::Box(_)
            | Self::Dyn(_)
            | Self::Impl(_)
            | Self::Ref(_) => false,
            Self::Ptr(_) => true,
            Self::Option(t) | Self::ManuallyDrop(t) => t.is_copyable(),
        }
    }

    pub(super) fn contains_impl(self) -> bool {
        match self {
            Self::File
            | Self::Stdin
            | Self::Stdout
            | Self::Stderr
            | Self::ChildStdin
            | Self::ChildStdout
            | Self::Dyn(_) => false,
            Self::Impl(_) => true,
            Self::Option(t)
            | Self::BufWriter(t)
            | Self::BufReader(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.contains_impl(),
        }
    }

    pub(super) fn get_dyn_bound(self) -> Option<TraitBound> {
        match self {
            Self::File
            | Self::Stdin
            | Self::Stdout
            | Self::Stderr
            | Self::ChildStdin
            | Self::ChildStdout
            | Self::Impl(_) => None,
            Self::Option(t)
            | Self::BufWriter(t)
            | Self::BufReader(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.get_dyn_bound(),
            Self::Dyn(traits) => Some(traits),
        }
    }
}

pub(super) fn convert_expr(
    to: StreamType<'_>,
    from: StreamType<'_>,
    expr: &str,
    consume: bool,
) -> String {
    tracing::info!("{} := {} // {}", to, from, consume);
    if to == from && (consume || from.is_copyable()) {
        return expr.to_string();
    }
    use StreamType::*;
    match (to, from) {
        (Option(to), Option(from)) => {
            if consume || from.is_copyable() {
                let body = convert_expr(*to, *from, "x", true);
                if to.contains_impl() {
                    format!("({}).map(|x| {})", expr, body)
                } else {
                    format!("({}).map::<{}, _>(|x| {})", expr, to, body)
                }
            } else {
                let body = convert_expr(*to, Ref(from), "x", true);
                if to.contains_impl() {
                    format!("({}).as_mut().map(|x| {})", expr, body)
                } else {
                    format!("({}).as_mut().map::<{}, _>(|x| {})", expr, to, body)
                }
            }
        }
        (Ptr(to), Option(from)) if to == from => {
            format!(
                "({}).as_mut().map_or(std::ptr::null_mut(), |r| r as *mut _)",
                expr
            )
        }
        (Ptr(to), Ref(from)) if to == from => {
            format!("&mut *({}) as *mut _", expr)
        }
        (to, Option(from)) => {
            if consume || from.is_copyable() {
                let unwrapped = format!("({}).unwrap()", expr);
                convert_expr(to, *from, &unwrapped, true)
            } else {
                let unwrapped = format!("({}).as_mut().unwrap()", expr);
                convert_expr(to, Ref(from), &unwrapped, true)
            }
        }
        (to, Ref(Option(from))) => {
            let unwrapped = format!("({}).as_mut().unwrap()", expr);
            convert_expr(to, Ref(from), &unwrapped, true)
        }
        (to, ManuallyDrop(from)) => {
            if consume {
                let unwrapped = format!("({}).take()", expr);
                convert_expr(to, *from, &unwrapped, true)
            } else {
                let unwrapped = format!("std::ops::DerefMut::deref_mut(&mut ({}))", expr);
                convert_expr(to, Ref(from), &unwrapped, true)
            }
        }
        (Option(to), from) => {
            let converted = convert_expr(*to, from, expr, consume);
            format!("Some({})", converted)
        }
        (ManuallyDrop(to), from) => {
            let converted = convert_expr(*to, from, expr, consume);
            format!("std::mem::ManuallyDrop::new({})", converted)
        }
        (
            Impl(_),
            File | Stdout | Stderr | ChildStdin | ChildStdout | BufWriter(_) | BufReader(_),
        ) => {
            if consume {
                expr.to_string()
            } else {
                format!("&mut ({})", expr)
            }
        }
        (
            Impl(_),
            Ref(File) | Ref(Stdout) | Ref(Stderr) | Ref(ChildStdin) | Ref(ChildStdout)
            | Ref(BufWriter(_)) | Ref(BufReader(_)),
        ) => expr.to_string(),
        (Impl(traits), Stdin) => {
            if traits.contains(StreamTrait::BufRead) {
                format!("({}).lock()", expr)
            } else if consume {
                expr.to_string()
            } else {
                format!("&mut ({})", expr)
            }
        }
        (Impl(_), Ref(Impl(_))) => {
            if consume {
                expr.to_string()
            } else {
                format!("&mut *({})", expr)
            }
        }
        (Impl(_), Ref(Box(Dyn(_)))) => {
            if consume {
                expr.to_string()
            } else {
                format!("&mut *({})", expr)
            }
        }
        (Impl(_), Ptr(Dyn(_))) => format!("&mut *({})", expr),
        (Impl(_), Ptr(from)) => {
            let r = format!("({}).as_mut()", expr);
            let from = Ref(from);
            convert_expr(to, Option(&from), &r, true)
        }
        (
            Box(Dyn(traits)),
            File | Stdin | Stdout | Stderr | ChildStdin | ChildStdout | BufWriter(_) | BufReader(_),
        ) => {
            assert!(consume);
            match from {
                File => {
                    if traits.contains(StreamTrait::Read) || traits.contains(StreamTrait::BufRead) {
                        return format!(
                            "{{ let stream: {} = Box::new(std::io::BufReader::new({})); stream }}",
                            to, expr
                        );
                    }
                    if traits.contains(StreamTrait::Write) {
                        return format!(
                            "{{ let stream: {} = Box::new(std::io::BufWriter::new({})); stream }}",
                            to, expr
                        );
                    }
                }
                Stdin => {
                    if traits.contains(StreamTrait::BufRead) {
                        return format!(
                            "{{ let stream: {} = Box::new(({}).lock()); stream }}",
                            to, expr
                        );
                    }
                }
                _ => {}
            }
            format!("{{ let stream: {} = Box::new({}); stream }}", to, expr)
        }
        (
            Ref(Dyn(_)),
            Ref(
                File | Stdin | Stdout | Stderr | ChildStdin | ChildStdout | BufWriter(_)
                | BufReader(_),
            ),
        ) => {
            format!("&mut *({})", expr)
        }
        (
            Ptr(Dyn(_)),
            Ref(
                File | Stdin | Stdout | Stderr | ChildStdin | ChildStdout | BufWriter(_)
                | BufReader(_),
            ),
        ) => {
            format!("&mut *({}) as *mut _", expr)
        }
        (Ptr(Dyn(to)), Ref(Box(Dyn(from)))) if to == from => {
            format!("&mut *({}) as *mut _", expr)
        }
        (
            Ref(Dyn(traits)),
            File | Stdin | Stdout | Stderr | ChildStdin | ChildStdout | BufWriter(_) | BufReader(_),
        ) => {
            if consume {
                let expr = convert_expr(Box(&Dyn(*traits)), from, expr, true);
                format!("Box::leak({})", expr)
            } else {
                format!("&mut ({})", expr)
            }
        }
        (
            Ptr(Dyn(traits)),
            File | Stdin | Stdout | Stderr | ChildStdin | ChildStdout | BufWriter(_) | BufReader(_),
        ) => {
            let expr = convert_expr(Ref(&Dyn(*traits)), from, expr, consume);
            format!("({}) as *mut _", expr)
        }
        (BufWriter(to), from) if *to == from => {
            assert!(consume);
            format!("std::io::BufWriter::new({})", expr)
        }
        (BufReader(to), from) if *to == from => {
            assert!(consume);
            format!("std::io::BufReader::new({})", expr)
        }
        _ => panic!("{} := {} // {}", to, from, consume),
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct IndicatorCheck<'a> {
    pub(super) name: &'a str,
    pub(super) eof: bool,
    pub(super) error: bool,
}

impl IndicatorCheck<'_> {
    #[inline]
    pub(super) fn has_check(&self) -> bool {
        self.eof || self.error
    }

    #[inline]
    pub(super) fn error_handling(&self) -> String {
        match (self.eof, self.error) {
            (true, true) => {
                format!(
                    "if e.kind() == std::io::ErrorKind::UnexpectedEof {{
    {0}_eof = 1;
}} else {{
    {0}_error = 1;
}}",
                    self.name
                )
            }
            (true, false) => {
                format!(
                    "if e.kind() == std::io::ErrorKind::UnexpectedEof {{ {}_eof = 1; }}",
                    self.name,
                )
            }
            (false, true) => {
                format!(
                    "if e.kind() != std::io::ErrorKind::UnexpectedEof {{ {}_error = 1; }}",
                    self.name
                )
            }
            (false, false) => "".to_string(),
        }
    }

    #[inline]
    pub(super) fn error_handling_no_eof(&self) -> String {
        if self.error {
            format!("{}_error = 1;", self.name)
        } else {
            "".to_string()
        }
    }

    #[inline]
    pub(super) fn clear(&self) -> String {
        match (self.eof, self.error) {
            (true, true) => format!("{{ {0}_eof = 0; {0}_error = 0; }}", self.name),
            (true, false) => format!("{{ {}_eof = 0; }}", self.name),
            (false, true) => format!("{{ {}_error = 0; }}", self.name),
            (false, false) => "()".to_string(),
        }
    }
}

pub(super) trait StreamExpr {
    fn expr(&self) -> String;
    fn ty(&self) -> StreamType<'_>;

    #[inline]
    fn borrow_for(&self, tr: StreamTrait) -> String {
        let to = StreamType::Impl(TraitBound::new([tr]));
        convert_expr(to, self.ty(), &self.expr(), false)
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct TypedExpr<'a> {
    expr: &'a Expr,
    ty: &'a StreamType<'a>,
}

impl<'a> TypedExpr<'a> {
    #[inline]
    pub(super) fn new(expr: &'a Expr, ty: &'a StreamType<'a>) -> Self {
        Self { expr, ty }
    }
}

impl StreamExpr for TypedExpr<'_> {
    #[inline]
    fn expr(&self) -> String {
        pprust::expr_to_string(self.expr)
    }

    #[inline]
    fn ty(&self) -> StreamType<'_> {
        *self.ty
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum StdStream {
    Stdin,
    Stdout,
    #[allow(unused)]
    Stderr,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct StdExpr(StdStream);

impl StdExpr {
    #[inline]
    pub(super) fn stdin() -> Self {
        Self(StdStream::Stdin)
    }

    #[inline]
    pub(super) fn stdout() -> Self {
        Self(StdStream::Stdout)
    }

    #[allow(unused)]
    #[inline]
    pub(super) fn stderr() -> Self {
        Self(StdStream::Stderr)
    }
}

impl StreamExpr for StdExpr {
    #[inline]
    fn expr(&self) -> String {
        match self.0 {
            StdStream::Stdin => "std::io::stdin()".to_string(),
            StdStream::Stdout => "std::io::stdout()".to_string(),
            StdStream::Stderr => "std::io::stderr()".to_string(),
        }
    }

    #[inline]
    fn ty(&self) -> StreamType<'_> {
        match self.0 {
            StdStream::Stdin => STDIN_TY,
            StdStream::Stdout => STDOUT_TY,
            StdStream::Stderr => STDERR_TY,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(super) enum StreamTrait {
    Read = 0,
    BufRead = 1,
    Write = 2,
    Seek = 3,
    AsRawFd = 4,
}

impl std::fmt::Display for StreamTrait {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Read => write!(f, "std::io::Read"),
            Self::BufRead => write!(f, "std::io::BufRead"),
            Self::Write => write!(f, "std::io::Write"),
            Self::Seek => write!(f, "std::io::Seek"),
            Self::AsRawFd => write!(f, "crate::AsRawFd"),
        }
    }
}

impl StreamTrait {
    const NUM: usize = 5;

    pub(super) fn from_permission(p: Permission) -> Option<Self> {
        match p {
            Permission::Read => Some(Self::Read),
            Permission::BufRead => Some(Self::BufRead),
            Permission::Write => Some(Self::Write),
            Permission::Seek => Some(Self::Seek),
            Permission::AsRawFd => Some(Self::AsRawFd),
            Permission::Lock | Permission::Close => None,
        }
    }

    fn short_name(self) -> &'static str {
        match self {
            Self::Read => "Read",
            Self::BufRead => "BufRead",
            Self::Write => "Write",
            Self::Seek => "Seek",
            Self::AsRawFd => "AsRawFd",
        }
    }
}

impl Idx for StreamTrait {
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
pub(super) struct TraitBound(BitSet8<StreamTrait>);

impl std::fmt::Display for TraitBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, t) in self.0.iter().enumerate() {
            if i != 0 {
                write!(f, " + ")?;
            }
            write!(f, "{}", t)?;
        }
        Ok(())
    }
}

impl Deref for TraitBound {
    type Target = BitSet8<StreamTrait>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TraitBound {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl TraitBound {
    #[inline]
    fn new<I: IntoIterator<Item = StreamTrait>>(traits: I) -> Self {
        Self(BitSet8::new(traits))
    }

    pub(super) fn trait_name(self) -> String {
        let mut name = String::new();
        for t in self.iter() {
            name.push_str(t.short_name());
        }
        name
    }
}
