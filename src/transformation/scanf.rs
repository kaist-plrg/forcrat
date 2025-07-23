pub(super) fn parse_specs(mut remaining: &[u8]) -> Vec<ConversionSpec> {
    let mut specs = vec![];
    loop {
        let res = parse_format(remaining);
        if let Some(rem) = res.remaining {
            remaining = rem;
            specs.push(res.conversion_spec.unwrap());
        } else {
            break specs;
        }
    }
}

struct ParseResult<'a> {
    #[allow(unused)]
    prefix: &'a [u8],
    conversion_spec: Option<ConversionSpec>,
    remaining: Option<&'a [u8]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Percent,
    Asterisk,
    Width,
    H,
    L,
    Conversion,
    Circumflex,
    ScanSet,
}

fn err(s: &[u8], i: Option<usize>) -> ! {
    panic!("{}", String::from_utf8_lossy(&s[i.unwrap()..]));
}

fn parse_format(s: &[u8]) -> ParseResult<'_> {
    let mut start_idx = None;
    let mut state = State::Percent;
    let mut assign = true;
    let mut width = None;
    let mut length = None;
    let mut conversion = None;
    for (i, c) in s.iter().enumerate() {
        if state == State::Percent {
            if *c == b'%' {
                start_idx = Some(i);
                state = State::Asterisk;
            }
        } else if matches!(state, State::Circumflex | State::ScanSet) {
            if *c == b'^' {
                if state == State::Circumflex {
                    let Some((Conversion::ScanSet(ScanSet { negative, .. }), _)) = &mut conversion
                    else {
                        unreachable!()
                    };
                    *negative = true;
                    state = State::ScanSet;
                } else {
                    err(s, start_idx);
                }
            } else if *c == b']' {
                if state == State::ScanSet {
                    let Some((_, old_i)) = &mut conversion else { unreachable!() };
                    *old_i = i;
                    break;
                } else {
                    err(s, start_idx);
                }
            } else {
                state = State::ScanSet;
                let Some((Conversion::ScanSet(ScanSet { chars, .. }), _)) = &mut conversion else {
                    unreachable!()
                };
                chars.push(*c);
            }
        } else if c.is_ascii_digit() {
            match state {
                State::Asterisk => {
                    width = Some((c - b'0') as usize);
                    state = State::Width;
                }
                State::Width => {
                    let Some(n) = width.as_mut() else { unreachable!() };
                    *n = *n * 10 + (c - b'0') as usize;
                }
                _ => err(s, start_idx),
            }
        } else if *c == b'*' {
            if state == State::Asterisk {
                assign = false;
                state = State::Width;
            } else {
                err(s, start_idx);
            }
        } else if let Some(len) = LengthMod::from_u8(*c) {
            match len {
                LengthMod::Short => match state {
                    State::Asterisk | State::Width => {
                        state = State::H;
                    }
                    State::H => {
                        length = Some(LengthMod::Char);
                        state = State::Conversion;
                    }
                    _ => err(s, start_idx),
                },
                LengthMod::Long => match state {
                    State::Asterisk | State::Width => {
                        state = State::L;
                    }
                    State::L => {
                        length = Some(LengthMod::LongLong);
                        state = State::Conversion;
                    }
                    _ => err(s, start_idx),
                },
                _ => {
                    length = Some(len);
                    state = State::Conversion;
                }
            }
        } else if let Some(conv) = Conversion::from_u8(*c) {
            match state {
                State::Asterisk | State::Width | State::Conversion => {}
                State::H => length = Some(LengthMod::Short),
                State::L => length = Some(LengthMod::Long),
                _ => err(s, start_idx),
            }
            let is_set = conv.is_set();
            conversion = Some((conv, i));
            if is_set {
                state = State::Circumflex;
            } else {
                break;
            }
        } else {
            err(s, start_idx);
        }
    }

    if let Some(start_idx) = start_idx {
        if let Some((conversion, last_idx)) = conversion {
            ParseResult {
                prefix: &s[..start_idx],
                conversion_spec: Some(ConversionSpec {
                    assign,
                    width,
                    length,
                    conversion,
                }),
                remaining: Some(&s[last_idx + 1..]),
            }
        } else {
            err(s, Some(start_idx))
        }
    } else {
        ParseResult {
            prefix: s,
            conversion_spec: None,
            remaining: None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LengthMod {
    Char,
    Short,
    Long,
    LongLong,
    IntMax,
    Size,
    PtrDiff,
    LongDouble,
}

impl std::fmt::Display for LengthMod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Char => write!(f, "hh"),
            Self::Short => write!(f, "h"),
            Self::Long => write!(f, "l"),
            Self::LongLong => write!(f, "ll"),
            Self::IntMax => write!(f, "j"),
            Self::Size => write!(f, "z"),
            Self::PtrDiff => write!(f, "t"),
            Self::LongDouble => write!(f, "L"),
        }
    }
}

impl LengthMod {
    #[inline]
    fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'h' => Some(Self::Short),
            b'l' => Some(Self::Long),
            b'j' => Some(Self::IntMax),
            b'z' => Some(Self::Size),
            b't' => Some(Self::PtrDiff),
            b'L' => Some(Self::LongDouble),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ScanSet {
    pub(super) negative: bool,
    pub(super) chars: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Conversion {
    Int10,
    Int0,
    Octal,
    Unsigned,
    Hexadecimal,
    Double,
    Str,
    ScanSet(ScanSet),
    Seq,
    Pointer,
    Num,
    C,
    S,
    Percent,
}

impl std::fmt::Display for Conversion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int10 => write!(f, "d"),
            Self::Int0 => write!(f, "i"),
            Self::Octal => write!(f, "o"),
            Self::Unsigned => write!(f, "u"),
            Self::Hexadecimal => write!(f, "x"),
            Self::Double => write!(f, "g"),
            Self::Str => write!(f, "s"),
            Self::ScanSet(ScanSet { negative, chars }) => {
                write!(f, "[")?;
                if *negative {
                    write!(f, "^")?;
                }
                for c in chars {
                    if let Some(s) = escape(*c) {
                        write!(f, "{s}")?;
                    } else {
                        write!(f, "{}", *c as char)?;
                    }
                }
                write!(f, "]")
            }
            Self::Seq => write!(f, "c"),
            Self::Pointer => write!(f, "p"),
            Self::Num => write!(f, "n"),
            Self::C => write!(f, "C"),
            Self::S => write!(f, "S"),
            Self::Percent => write!(f, "%"),
        }
    }
}

impl Conversion {
    #[inline]
    fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'd' => Some(Self::Int10),
            b'i' => Some(Self::Int0),
            b'o' => Some(Self::Octal),
            b'u' => Some(Self::Unsigned),
            b'x' => Some(Self::Hexadecimal),
            b'a' | b'e' | b'f' | b'g' => Some(Self::Double),
            b's' => Some(Self::Str),
            b'[' => Some(Self::ScanSet(ScanSet {
                negative: false,
                chars: vec![],
            })),
            b'c' => Some(Self::Seq),
            b'p' => Some(Self::Pointer),
            b'n' => Some(Self::Num),
            b'C' => Some(Self::C),
            b'S' => Some(Self::S),
            b'%' => Some(Self::Percent),
            _ => None,
        }
    }

    #[inline]
    fn is_set(&self) -> bool {
        matches!(self, Self::ScanSet { .. })
    }

    fn ty(&self, length: Option<LengthMod>) -> &'static str {
        use LengthMod::*;
        match self {
            Self::Int10 | Self::Int0 => match length {
                None => "i32",
                Some(Char) => "i8",
                Some(Short) => "i16",
                Some(Long | LongLong | IntMax | Size) => "i64",
                Some(PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Octal | Self::Unsigned | Self::Hexadecimal => match length {
                None => "u32",
                Some(Char) => "u8",
                Some(Short) => "u16",
                Some(Long | LongLong | IntMax | Size | PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Double => match length {
                None => "f32",
                Some(Long) => "f64",
                Some(LongDouble) => "f128::f128",
                _ => panic!(),
            },
            Self::Str | Self::ScanSet { .. } => "&str",
            Self::Seq | Self::Pointer | Self::C | Self::S | Self::Num | Self::Percent => {
                unimplemented!()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ConversionSpec {
    pub(super) assign: bool,
    pub(super) width: Option<usize>,
    length: Option<LengthMod>,
    conversion: Conversion,
}

impl std::fmt::Display for ConversionSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%")?;
        if !self.assign {
            write!(f, "*")?;
        }
        if let Some(width) = self.width {
            write!(f, "{width}")?;
        }
        if let Some(length) = self.length {
            write!(f, "{length}")?;
        }
        write!(f, "{}", self.conversion)
    }
}

impl ConversionSpec {
    pub(super) fn ty(&self) -> &'static str {
        self.conversion.ty(self.length)
    }

    pub(super) fn scan_set(&self) -> Option<&ScanSet> {
        match &self.conversion {
            Conversion::ScanSet(set) => Some(set),
            _ => None,
        }
    }
}

pub(super) fn escape(c: u8) -> Option<&'static str> {
    match c {
        b'\n' => Some("\\n"),
        b'\r' => Some("\\r"),
        b'\t' => Some("\\t"),
        b'\\' => Some("\\\\"),
        b'\'' => Some("\\'"),
        b'\"' => Some("\\\""),
        b'\0' => Some("\\0"),
        _ => None,
    }
}

#[cfg(test)]
fn test_helper(s: &str) -> ConversionSpec {
    let res = parse_format(s.as_bytes());
    let empty: &[u8] = &[];
    assert_eq!(res.prefix, empty, "{:?}", s);
    assert_eq!(res.remaining, Some(empty), "{:?}", s);
    res.conversion_spec.expect(s)
}

#[cfg(test)]
#[test]
fn test_scanf_parse() {
    assert_eq!(
        test_helper("%d"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::Int10
        }
    );
    assert_eq!(
        test_helper("%ld"),
        ConversionSpec {
            assign: true,
            width: None,
            length: Some(LengthMod::Long),
            conversion: Conversion::Int10
        }
    );
    assert_eq!(
        test_helper("%hhd"),
        ConversionSpec {
            assign: true,
            width: None,
            length: Some(LengthMod::Char),
            conversion: Conversion::Int10
        }
    );
    assert_eq!(
        test_helper("%10s"),
        ConversionSpec {
            assign: true,
            width: Some(10),
            length: None,
            conversion: Conversion::Str
        }
    );
    assert_eq!(
        test_helper("%*s"),
        ConversionSpec {
            assign: false,
            width: None,
            length: None,
            conversion: Conversion::Str
        }
    );
    assert_eq!(
        test_helper("%[abcd]"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::ScanSet(ScanSet {
                negative: false,
                chars: vec![b'a', b'b', b'c', b'd']
            })
        }
    );
    assert_eq!(
        test_helper("%[^\n]"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::ScanSet(ScanSet {
                negative: true,
                chars: vec![b'\n']
            })
        }
    );
}
