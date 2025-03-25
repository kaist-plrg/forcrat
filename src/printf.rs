pub fn to_rust_format(mut remaining: &str) -> (String, Vec<&'static str>) {
    let mut format = String::new();
    let mut casts = vec![];
    loop {
        let res = parse_format(remaining);
        for c in res.prefix.chars() {
            match c {
                '{' => format.push_str("{{"),
                '}' => format.push_str("}}"),
                _ => format.push(c),
            }
        }
        if let Some(cs) = res.conversion_spec {
            let mut fmt = String::new();
            let mut conv = String::new();
            for flag in cs.flags {
                match flag {
                    FlagChar::Apostrophe => todo!(),
                    FlagChar::Minus => fmt.push('<'),
                    FlagChar::Plus => fmt.push('+'),
                    FlagChar::Space => todo!(),
                    FlagChar::Hash => fmt.push('#'),
                    FlagChar::Zero => fmt.push('0'),
                }
            }
            if let Some(width) = cs.width {
                match width {
                    Width::Asterisk => todo!(),
                    Width::Decimal(n) => fmt.push_str(&n.to_string()),
                }
            }
            if let Some(precision) = cs.precision {
                fmt.push('.');
                match precision {
                    Width::Asterisk => fmt.push('*'),
                    Width::Decimal(n) => fmt.push_str(&n.to_string()),
                }
            }
            match cs.conversion {
                Conversion::Int | Conversion::Unsigned | Conversion::Char | Conversion::Str => {}
                Conversion::Octal => fmt.push('o'),
                Conversion::Hexadecimal => fmt.push('x'),
                Conversion::HexadecimalUpper => fmt.push('X'),
                Conversion::Double => {
                    if cs.precision.is_none() {
                        fmt.push_str(".6");
                    }
                }
                Conversion::DoubleExp => fmt.push('e'),
                Conversion::DoubleAuto => todo!(),
                Conversion::DoubleError => todo!(),
                Conversion::Pointer => fmt.push_str("#x"),
                Conversion::Num | Conversion::C | Conversion::S => unimplemented!(),
                Conversion::Percent => conv = "%".to_string(),
            }
            if conv.is_empty() {
                conv.push('{');
                if !fmt.is_empty() {
                    conv.push(':');
                    conv.push_str(&fmt);
                }
                conv.push('}');
            }
            format.push_str(&conv);
            if let Some(cast) = cs.conversion.ty(cs.length) {
                casts.push(cast);
            }
        }
        if let Some(rem) = res.remaining {
            remaining = rem;
        } else {
            break;
        }
    }
    assert!(format.ends_with("\\0"));
    format.pop();
    format.pop();
    (format, casts)
}

pub struct ParseResult<'a> {
    pub prefix: &'a str,
    pub conversion_spec: Option<ConversionSpec>,
    pub remaining: Option<&'a str>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Percent,
    Flag,
    Width,
    Period,
    Precision,
    Length,
    H,
    L,
    Conversion,
}

pub fn parse_format(s: &str) -> ParseResult<'_> {
    let mut start_idx = None;
    let mut state = State::Percent;
    let mut flags = vec![];
    let mut width = None;
    let mut precision = None;
    let mut length = None;
    let mut conversion = None;
    for (i, c) in s.chars().enumerate() {
        if state == State::Percent {
            if c == '%' {
                start_idx = Some(i);
                state = State::Flag;
            }
        } else if ('1'..='9').contains(&c) || (c == '0' && state != State::Flag) {
            match state {
                State::Flag => {
                    width = Some(Width::Decimal(c as usize - '0' as usize));
                    state = State::Width;
                }
                State::Width => {
                    let Some(Width::Decimal(n)) = &mut width else { unreachable!() };
                    *n = *n * 10 + (c as usize - '0' as usize);
                }
                State::Precision => match &mut precision {
                    None => precision = Some(Width::Decimal(c as usize - '0' as usize)),
                    Some(Width::Decimal(n)) => *n = *n * 10 + (c as usize - '0' as usize),
                    _ => unreachable!(),
                },
                _ => panic!("{}", s),
            }
        } else if let Some(flag) = FlagChar::from_char(c) {
            flags.push(flag);
        } else if c == '*' {
            match state {
                State::Flag => {
                    width = Some(Width::Asterisk);
                    state = State::Period;
                }
                State::Precision => {
                    precision = Some(Width::Asterisk);
                    state = State::Length;
                }
                _ => panic!("{}", s),
            }
        } else if c == '.' {
            if matches!(state, State::Flag | State::Width | State::Period) {
                state = State::Precision;
            } else {
                panic!("{}", s);
            }
        } else if let Some(len) = LengthMod::from_char(c) {
            match len {
                LengthMod::Short => match state {
                    State::Flag
                    | State::Width
                    | State::Period
                    | State::Precision
                    | State::Length => {
                        state = State::H;
                    }
                    State::H => {
                        length = Some(LengthMod::Char);
                        state = State::Conversion;
                    }
                    _ => panic!("{}", s),
                },
                LengthMod::Long => match state {
                    State::Flag
                    | State::Width
                    | State::Period
                    | State::Precision
                    | State::Length => {
                        state = State::L;
                    }
                    State::L => {
                        length = Some(LengthMod::LongLong);
                        state = State::Conversion;
                    }
                    _ => panic!("{}", s),
                },
                _ => {
                    length = Some(len);
                    state = State::Conversion;
                }
            }
        } else if let Some(conv) = Conversion::from_char(c) {
            match state {
                State::Flag
                | State::Width
                | State::Period
                | State::Precision
                | State::Length
                | State::Conversion => {
                    conversion = Some((conv, i));
                    break;
                }
                State::H => {
                    length = Some(LengthMod::Short);
                    conversion = Some((conv, i));
                    break;
                }
                State::L => {
                    length = Some(LengthMod::Long);
                    conversion = Some((conv, i));
                    break;
                }
                _ => unreachable!(),
            }
        }
    }

    if let Some(start_idx) = start_idx {
        if let Some((conversion, last_idx)) = conversion {
            ParseResult {
                prefix: &s[..start_idx],
                conversion_spec: Some(ConversionSpec {
                    flags,
                    width,
                    precision,
                    length,
                    conversion,
                }),
                remaining: Some(&s[last_idx + 1..]),
            }
        } else {
            panic!("{}", s);
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
enum FlagChar {
    Apostrophe,
    Minus,
    Plus,
    Space,
    Hash,
    Zero,
}

impl std::fmt::Display for FlagChar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Apostrophe => write!(f, "'"),
            Self::Minus => write!(f, "-"),
            Self::Plus => write!(f, "+"),
            Self::Space => write!(f, " "),
            Self::Hash => write!(f, "#"),
            Self::Zero => write!(f, "0"),
        }
    }
}

impl FlagChar {
    #[inline]
    fn from_char(c: char) -> Option<Self> {
        match c {
            '\'' => Some(Self::Apostrophe),
            '-' => Some(Self::Minus),
            '+' => Some(Self::Plus),
            ' ' => Some(Self::Space),
            '#' => Some(Self::Hash),
            '0' => Some(Self::Zero),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Width {
    Asterisk,
    Decimal(usize),
}

impl std::fmt::Display for Width {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Width::Asterisk => write!(f, "*"),
            Width::Decimal(n) => write!(f, "{}", n),
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
    fn from_char(c: char) -> Option<Self> {
        match c {
            'h' => Some(Self::Short),
            'l' => Some(Self::Long),
            'j' => Some(Self::IntMax),
            'z' => Some(Self::Size),
            't' => Some(Self::PtrDiff),
            'L' => Some(Self::LongDouble),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Conversion {
    Int,
    Octal,
    Unsigned,
    Hexadecimal,
    HexadecimalUpper,
    Double,
    DoubleExp,
    DoubleAuto,
    DoubleError,
    Char,
    Str,
    Pointer,
    Num,
    C,
    S,
    Percent,
}

impl std::fmt::Display for Conversion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int => write!(f, "d"),
            Self::Octal => write!(f, "o"),
            Self::Unsigned => write!(f, "u"),
            Self::Hexadecimal => write!(f, "x"),
            Self::HexadecimalUpper => write!(f, "X"),
            Self::Double => write!(f, "f"),
            Self::DoubleExp => write!(f, "e"),
            Self::DoubleAuto => write!(f, "g"),
            Self::DoubleError => write!(f, "a"),
            Self::Char => write!(f, "c"),
            Self::Str => write!(f, "s"),
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
    fn from_char(c: char) -> Option<Self> {
        match c {
            'd' | 'i' => Some(Self::Int),
            'o' => Some(Self::Octal),
            'u' => Some(Self::Unsigned),
            'x' => Some(Self::Hexadecimal),
            'X' => Some(Self::HexadecimalUpper),
            'f' | 'F' => Some(Self::Double),
            'e' | 'E' => Some(Self::DoubleExp),
            'g' | 'G' => Some(Self::DoubleAuto),
            'a' | 'A' => Some(Self::DoubleError),
            'c' => Some(Self::Char),
            's' => Some(Self::Str),
            'p' => Some(Self::Pointer),
            'n' => Some(Self::Num),
            'C' => Some(Self::C),
            'S' => Some(Self::S),
            '%' => Some(Self::Percent),
            _ => None,
        }
    }

    fn ty(self, length: Option<LengthMod>) -> Option<&'static str> {
        use LengthMod::*;
        let t = match self {
            Self::Int => match length {
                None => "i32",
                Some(Char) => "i8",
                Some(Short) => "i16",
                Some(Long | LongLong | IntMax | Size) => "i64",
                Some(PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Octal | Self::Unsigned | Self::Hexadecimal | Self::HexadecimalUpper => {
                match length {
                    None => "u32",
                    Some(Char) => "u8",
                    Some(Short) => "u16",
                    Some(Long | LongLong | IntMax | Size | PtrDiff) => "u64",
                    Some(LongDouble) => panic!(),
                }
            }
            Self::Double | Self::DoubleExp | Self::DoubleAuto | Self::DoubleError => match length {
                None => "f64",
                Some(LongDouble) => "f128::f128",
                _ => panic!(),
            },
            Self::Char => "char",
            Self::Str => "&str",
            Self::Pointer => "usize",
            Self::C | Self::S => unimplemented!(),
            Self::Num | Self::Percent => return None,
        };
        Some(t)
    }
}

#[derive(Debug, Clone)]
pub struct ConversionSpec {
    flags: Vec<FlagChar>,
    width: Option<Width>,
    precision: Option<Width>,
    length: Option<LengthMod>,
    conversion: Conversion,
}

impl std::fmt::Display for ConversionSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%")?;
        for flag in &self.flags {
            write!(f, "{}", flag)?;
        }
        if let Some(width) = self.width {
            write!(f, "{}", width)?;
        }
        if let Some(precision) = self.precision {
            write!(f, ".{}", precision)?;
        }
        if let Some(length) = self.length {
            write!(f, "{}", length)?;
        }
        write!(f, "{}", self.conversion)
    }
}
