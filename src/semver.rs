//! Implements https://semver.org/spec/v2.0.0.html
//!
//! Backus–Naur Form Grammar for Valid SemVer Versions
//!
//!    <valid semver> ::= <version core>
//!                     | <version core> "-" <pre-release>
//!                     | <version core> "+" <build>
//!                     | <version core> "-" <pre-release> "+" <build>
//!    
//!    <version core> ::= <major> "." <minor> "." <patch>
//!    
//!    <major> ::= <numeric identifier>
//!    
//!    <minor> ::= <numeric identifier>
//!    
//!    <patch> ::= <numeric identifier>
//!    
//!    <pre-release> ::= <dot-separated pre-release identifiers>
//!    
//!    <dot-separated pre-release identifiers> ::= <pre-release identifier>
//!                                              | <pre-release identifier> "." <dot-separated pre-release identifiers>
//!    
//!    <build> ::= <dot-separated build identifiers>
//!    
//!    <dot-separated build identifiers> ::= <build identifier>
//!                                        | <build identifier> "." <dot-separated build identifiers>
//!    
//!    <pre-release identifier> ::= <alphanumeric identifier>
//!                               | <numeric identifier>
//!    
//!    <build identifier> ::= <alphanumeric identifier>
//!                         | <digits>
//!    
//!    <alphanumeric identifier> ::= <non-digit>
//!                                | <non-digit> <identifier characters>
//!                                | <identifier characters> <non-digit>
//!                                | <identifier characters> <non-digit> <identifier characters>
//!    
//!    <numeric identifier> ::= "0"
//!                           | <positive digit>
//!                           | <positive digit> <digits>
//!    
//!    <identifier characters> ::= <identifier character>
//!                              | <identifier character> <identifier characters>
//!    
//!    <identifier character> ::= <digit>
//!                             | <non-digit>
//!    
//!    <non-digit> ::= <letter>
//!                  | "-"
//!    
//!    <digits> ::= <digit>
//!               | <digit> <digits>
//!    
//!    <digit> ::= "0"
//!              | <positive digit>
//!    
//!    <positive digit> ::= "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
//!    
//!    <letter> ::= "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J"
//!               | "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T"
//!               | "U" | "V" | "W" | "X" | "Y" | "Z" | "a" | "b" | "c" | "d"
//!               | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n"
//!               | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x"
//!               | "y" | "z"

use std::{convert::{TryFrom, TryInto}, fmt::{Debug, Display}, str::FromStr};

use thiserror::Error;

#[derive(Clone)]
pub struct SemVer {
    pub(crate) major: usize,
    pub(crate) minor: usize,
    pub(crate) patch: usize,
    pub(crate) pre: Vec<PreReleaseIdentifier>,
    pub(crate) build: Vec<BuildIdentifier>,
}

impl SemVer {

    pub const fn is_pre_major(&self) -> bool {
        self.major == 0
    }

    pub fn is_prerelease(&self) -> bool {
        !self.pre.is_empty()
    }

    pub fn increment_major(&mut self) {
        self.major+=1;
        self.minor= 0;
        self.patch = 0;
    }


    pub fn increment_minor(&mut self) {
        self.minor+= 1;
        self.patch = 0;
    }

    pub fn increment_patch(&mut self) {
        self.patch += 1;
    }
}


impl Default for SemVer {
    fn default() -> Self {
        Self {
            major: 0,
            minor: 1,
            patch: 0,
            pre: Vec::new(),
            build: Vec::new(),
        }
    }
}

impl Display for SemVer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        if !self.pre.is_empty() {
            let mut it = self.pre.iter();
            let first = it.next().unwrap();
            write!(f, "-{}", first)?;
            for pre in it {
                write!(f, ".{}", pre)?;
            }
        }
        if !self.build.is_empty() {
            let mut it = self.build.iter();
            let first = it.next().unwrap();
            write!(f, "+{}", first.0)?;
            for build in it {
                write!(f, ".{}", build.0)?;
            }
        }
        Ok(())
    }
}

impl Debug for SemVer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl PartialOrd for SemVer {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SemVer {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.major.cmp(&other.major) {
            std::cmp::Ordering::Equal => {}
            ord => {
                return ord;
            }
        }
        match self.minor.cmp(&other.minor) {
            std::cmp::Ordering::Equal => {}
            ord => {
                return ord;
            }
        }
        match self.patch.cmp(&other.patch) {
            std::cmp::Ordering::Equal => {}
            ord => {
                return ord;
            }
        }

        match (self.pre.as_slice(), other.pre.as_slice()) {
            ([], []) => std::cmp::Ordering::Equal,
            ([], _) => std::cmp::Ordering::Greater,
            (_, []) => std::cmp::Ordering::Less,
            (a, b) => a.cmp(&b),
        }
    }
}

impl PartialEq for SemVer {
    fn eq(&self, other: &Self) -> bool {
        self.major == other.major
            && self.minor == other.minor
            && self.patch == other.patch
            && self.pre == other.pre
    }
}

impl Eq for SemVer {}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PreReleaseIdentifier {
    Numeric(usize),
    AlphaNumeric(String),
}

impl Display for PreReleaseIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PreReleaseIdentifier::Numeric(n) => {
                write!(f, "{}", n)
            }
            PreReleaseIdentifier::AlphaNumeric(s) => {
                write!(f, "{}", s)
            }
        }
    }
}
#[derive(Clone)]
pub struct BuildIdentifier(String);

#[derive(Debug, PartialEq, Eq, Error)]
pub enum SemVerErr {
    #[error("length should be at least 5 bytes")]
    AtLeast5Bytes,
    #[error("expected dot at byte offset {0}")]
    ExpectedDot(usize),
    #[error("expected numeric identifier at byte offset {0}")]
    ExpectedNumericIdentifier(usize),
    #[error("expected a - or + at byte offset {0}")]
    ExpectedPlusOrMin(usize),
    #[error("non ascii alphanumeric or hyphen character at byte offset {0}")]
    NonAscii(usize),
    #[error("empty identifier at offset {0}")]
    EmptyIdentifier(usize),
    #[error("the integer at byte offset {0} should not contain")]
    LeadingZero(usize),
}

impl TryFrom<&str> for SemVer {
    type Error = SemVerErr;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        fn parse_numeric_identifier<'a>(
            orig: &'a str,
            s: &'a str,
        ) -> Result<(usize, &'a str), SemVerErr> {
            let bytes = s.as_bytes();
            let it = bytes.iter();
            let n = it.take_while(|x| matches!(x, b'0'..=b'9')).count();
            if let Ok(i) = s[0..n].parse() {
                match bytes {
                    [b'0', b'1'..=b'9', ..] => Err(SemVerErr::LeadingZero(offset(orig, s))),
                    _ => Ok((i, &s[n..])),
                }
            } else {
                Err(SemVerErr::ExpectedNumericIdentifier(offset(orig, s)))
            }
        }
        fn parse_build(s: &str) -> Result<Vec<BuildIdentifier>, SemVerErr> {
            s.split('.')
                .into_iter()
                .map(|meta| {
                    if meta.is_empty() {
                        Err(SemVerErr::EmptyIdentifier(offset(s, meta)))
                    } else {
                        let n_alnum = meta
                            .as_bytes()
                            .iter()
                            .take_while(
                                |x| matches!(x,  b'0'..=b'9'|b'a'..=b'z' | b'A'..=b'Z' | b'-'),
                            )
                            .count();
                        if n_alnum == meta.len() {
                            Ok(BuildIdentifier(meta.to_owned()))
                        } else {
                            Err(SemVerErr::NonAscii(offset(s, &meta[n_alnum..])))
                        }
                    }
                })
                .collect()
        }
        fn parse_pre_release<'a>(
            s: &'a str,
            rest: &'a str,
        ) -> Result<Vec<PreReleaseIdentifier>, SemVerErr> {
            rest.split('.')
                .into_iter()
                .map(|meta| {
                    if meta.is_empty() {
                        return Err(SemVerErr::EmptyIdentifier(offset(s, meta)));
                    }

                    let n_numeric = meta.as_bytes().iter().enumerate().try_fold(
                        0usize,
                        |n, (i, x)| match x {
                            b'0'..=b'9' => Ok(n + 1),
                            b'a'..=b'z' | b'A'..=b'Z' | b'-' => Ok(n),
                            _ => Err(SemVerErr::NonAscii(offset(s, &meta[i..]))),
                        },
                    )?;
                    if meta.len() == n_numeric {
                        let (n, _) = parse_numeric_identifier(s, meta)?;
                        Ok(PreReleaseIdentifier::Numeric(n))
                    } else {
                        Ok(PreReleaseIdentifier::AlphaNumeric(meta.to_owned()))
                    }
                })
                .collect()
        }
        fn expect_dot<'a>(s: &'a str, rest: &'a str) -> Result<&'a str, SemVerErr> {
            match rest.as_bytes().get(0) {
                Some(b'.') => Ok(&rest[1..]),
                _ => Err(SemVerErr::ExpectedDot(offset(s, rest))),
            }
        }
        fn offset(from: &str, to: &str) -> usize {
            to.as_ptr() as usize - from.as_ptr() as usize
        }
        if s.len() < 5 {
            return Err(SemVerErr::AtLeast5Bytes);
        }
        let (major, rest) = parse_numeric_identifier(s, s)?;
        let rest = expect_dot(s, rest)?;
        let (minor, rest) = parse_numeric_identifier(s, rest)?;
        let rest = expect_dot(s, rest)?;
        let (patch, rest) = parse_numeric_identifier(s, rest)?;
        match rest.as_bytes().get(0) {
            Some(b'-') => {
                let rest = &rest[1..];
                let mut split_build = rest.split('+');
                let pre_release = parse_pre_release(s, split_build.next().unwrap())?;
                let build = if let Some(build) = split_build.next() {
                    let build = parse_build(build)?;
                    match split_build.next() {
                        Some(build) => return Err(SemVerErr::NonAscii(offset(s, build))),
                        None => build,
                    }
                } else {
                    Vec::new()
                };

                Ok(SemVer {
                    minor,
                    major,
                    patch,
                    pre: pre_release,
                    build,
                })
            }
            Some(b'+') => {
                let rest = &rest[1..];
                let build = parse_build(rest)?;
                Ok(SemVer {
                    minor,
                    major,
                    patch,
                    build,
                    ..Default::default()
                })
            }
            None => {
                Ok(SemVer {
                    major,
                    minor,
                    patch,
                    ..Default::default()
                })
            }
            _ => Err(SemVerErr::ExpectedPlusOrMin(offset(s, rest))),
        }
    }
}

impl FromStr for SemVer {
    type Err = SemVerErr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.try_into()
    }
}

#[cfg(test)]
mod tests {

    use std::convert::TryInto;

    use super::*;

    fn v(s: &str) -> SemVer {
        s.try_into().unwrap()
    }

    #[test]
    fn test_parse() {
        assert_eq!(SemVer::default(), v("0.1.0"));
        assert_eq!(
            SemVer {
                major: 21,
                minor: 11,
                patch: 10,
                ..Default::default()
            },
            v("21.11.10")
        );
    }

    #[test]
    fn test_order() {
        assert!(v("1.0.0") < v("2.0.0"));
        assert!(v("2.0.0") < v("2.1.0"));
        assert!(v("2.1.0") < v("2.1.1"));
        assert!(v("2.0.0") > v("1.0.0"));
        assert!(v("2.1.0") > v("2.0.0"));
        assert!(v("2.1.1") > v("2.1.0"));
    }

    #[test]
    fn test_invalid() {
        assert!(!SemVer::try_from("").is_ok());
        assert!(!SemVer::try_from("1.0").is_ok());
        assert!(!SemVer::try_from("1.0.").is_ok());
        assert!(!SemVer::try_from("10000").is_ok());
        assert!(!SemVer::try_from("1.0.0.0").is_ok());
    }

    #[test]
    fn test_invalid_leading_zero() {
        let err = SemVerErr::LeadingZero(2);
        assert_eq!(err, SemVer::try_from("0.01.0").unwrap_err());
    }
    mod build_meta {

        use super::*;

        #[test]
        fn test_build_meta() {
            let default = SemVer {
                major: 1,
                minor: 0,
                ..Default::default()
            };
            assert_eq!(
                SemVer {
                    pre: vec![PreReleaseIdentifier::AlphaNumeric("alpha".to_owned())],
                    build: vec![BuildIdentifier("001".to_owned())],
                    ..default.clone()
                },
                v("1.0.0-alpha+001")
            );
            assert_eq!(
                SemVer {
                    build: vec![BuildIdentifier("20130313144700".to_string())],
                    ..default.clone()
                },
                v("1.0.0+20130313144700")
            );
            assert_eq!(
                SemVer {
                    pre: vec![PreReleaseIdentifier::AlphaNumeric("beta".to_string())],
                    build: vec![
                        BuildIdentifier("exp".to_string()),
                        BuildIdentifier("sha".to_string()),
                        BuildIdentifier("5114f85".to_string())
                    ],
                    ..default.clone()
                },
                v("1.0.0-beta+exp.sha.5114f85")
            );
            assert_eq!(
                SemVer {
                    build: vec![BuildIdentifier("21AF26D3----117B344092BD".to_string())],
                    ..default.clone()
                },
                v("1.0.0+21AF26D3----117B344092BD")
            );
        }

        #[test]
        fn test_order_build_meta() {
            let v_1_0_0: SemVer = v("1.0.0");
            let v_1_0_0_1a2b3c: SemVer = v("1.0.0+1a2b3c");
            assert!(v_1_0_0 == v_1_0_0_1a2b3c);
        }
    }

    mod pre_release {

        use super::*;

        #[test]
        fn test_parse_pre_release() {
            let default = SemVer {
                major: 1,
                minor: 0,
                ..Default::default()
            };
            assert_eq!(
                SemVer {
                    pre: vec![PreReleaseIdentifier::AlphaNumeric("alpha".to_string())],
                    ..default.clone()
                },
                v("1.0.0-alpha")
            );
            assert_eq!(
                SemVer {
                    pre: vec![
                        PreReleaseIdentifier::AlphaNumeric("alpha".to_string()),
                        PreReleaseIdentifier::Numeric(1)
                    ],
                    ..default.clone()
                },
                v("1.0.0-alpha.1")
            );
            assert_eq!(
                SemVer {
                    pre: vec![
                        PreReleaseIdentifier::Numeric(0),
                        PreReleaseIdentifier::Numeric(3),
                        PreReleaseIdentifier::Numeric(7)
                    ],
                    ..default.clone()
                },
                v("1.0.0-0.3.7")
            );
            assert_eq!(
                SemVer {
                    pre: vec![
                        PreReleaseIdentifier::AlphaNumeric("x".to_string()),
                        PreReleaseIdentifier::Numeric(7),
                        PreReleaseIdentifier::AlphaNumeric("z".to_string()),
                        PreReleaseIdentifier::Numeric(92)
                    ],
                    ..default.clone()
                },
                v("1.0.0-x.7.z.92")
            );
            assert_eq!(
                SemVer {
                    pre: vec![
                        PreReleaseIdentifier::AlphaNumeric("x-y-z".to_string()),
                        PreReleaseIdentifier::AlphaNumeric("--".to_string())
                    ],
                    ..default
                },
                v("1.0.0-x-y-z.--")
            );
        }

        #[test]
        fn test_order_pre_release() {
            // lt
            assert!(v("1.0.0-alpha") < v("1.0.0-alpha.1"));
            assert!(v("1.0.0-alpha.1") < v("1.0.0-alpha.beta"));
            assert!(v("1.0.0-alpha.beta") < v("1.0.0-beta"));
            assert!(v("1.0.0-beta") < v("1.0.0-beta.2"));
            assert!(v("1.0.0-beta.2") < v("1.0.0-beta.11"));
            assert!(v("1.0.0-beta.11") < v("1.0.0-rc.1"));
            assert!(v("1.0.0-rc.1") < v("1.0.0"));
            // gt
            assert!(v("1.0.0-alpha.1") > v("1.0.0-alpha"));
            assert!(v("1.0.0-alpha.beta") > v("1.0.0-alpha.1"));
            assert!(v("1.0.0-beta") > v("1.0.0-alpha.beta"));
            assert!(v("1.0.0-beta.2") > v("1.0.0-beta"));
            assert!(v("1.0.0-beta.11") > v("1.0.0-beta.2"));
            assert!(v("1.0.0-rc.1") > v("1.0.0-beta.11"));
            assert!(v("1.0.0") > v("1.0.0-rc.1"));
        }

        #[test]
        fn test_pre_release_no_ascii() {
            assert_eq!(
                SemVerErr::NonAscii(6),
                SemVer::try_from("1.0.0-άλφα").unwrap_err()
            );
        }

        #[test]
        fn test_pre_release_empty() {
            assert_eq!(
                SemVerErr::EmptyIdentifier(8),
                SemVer::try_from("1.0.0-a..b").unwrap_err()
            );
        }

        #[test]
        fn test_pre_release_leading_zero() {
            assert_eq!(
                SemVerErr::LeadingZero(12),
                SemVer::try_from("1.0.0-alpha.01").unwrap_err()
            );
            assert!(SemVer::try_from("1.0.0-alpha.01a").is_ok());
        }
    }

    mod test_vectors {
        // from https://regex101.com/r/Ly7O1x/3/
        use super::*;

        #[test]
        fn valid() {
            assert!(SemVer::try_from("0.0.4").is_ok(), "0.0.4 is valid");
            assert!(SemVer::try_from("1.2.3").is_ok(), "1.2.3 is valid");
            assert!(SemVer::try_from("10.20.30").is_ok(), "10.20.30 is valid");
            assert!(
                SemVer::try_from("1.1.2-prerelease+meta").is_ok(),
                "1.1.2-prerelease+meta is valid"
            );
            assert!(
                SemVer::try_from("1.1.2+meta").is_ok(),
                "1.1.2+meta is valid"
            );
            assert!(
                SemVer::try_from("1.1.2+meta-valid").is_ok(),
                "1.1.2+meta-valid is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha").is_ok(),
                "1.0.0-alpha is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-beta").is_ok(),
                "1.0.0-beta is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha.beta").is_ok(),
                "1.0.0-alpha.beta is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha.beta.1").is_ok(),
                "1.0.0-alpha.beta.1 is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha.1").is_ok(),
                "1.0.0-alpha.1 is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha0.valid").is_ok(),
                "1.0.0-alpha0.valid is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha.0valid").is_ok(),
                "1.0.0-alpha.0valid is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha-a.b-c-somethinglong+build.1-aef.1-its-okay").is_ok(),
                "1.0.0-alpha-a.b-c-somethinglong+build.1-aef.1-its-okay is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-rc.1+build.1").is_ok(),
                "1.0.0-rc.1+build.1 is valid"
            );
            assert!(
                SemVer::try_from("2.0.0-rc.1+build.123").is_ok(),
                "2.0.0-rc.1+build.123 is valid"
            );
            assert!(
                SemVer::try_from("1.2.3-beta").is_ok(),
                "1.2.3-beta is valid"
            );
            assert!(
                SemVer::try_from("10.2.3-DEV-SNAPSHOT").is_ok(),
                "10.2.3-DEV-SNAPSHOT is valid"
            );
            assert!(
                SemVer::try_from("1.2.3-SNAPSHOT-123").is_ok(),
                "1.2.3-SNAPSHOT-123 is valid"
            );
            assert!(SemVer::try_from("1.0.0").is_ok(), "1.0.0 is valid");
            assert!(SemVer::try_from("2.0.0").is_ok(), "2.0.0 is valid");
            assert!(SemVer::try_from("1.1.7").is_ok(), "1.1.7 is valid");
            assert!(
                SemVer::try_from("2.0.0+build.1848").is_ok(),
                "2.0.0+build.1848 is valid"
            );
            assert!(
                SemVer::try_from("2.0.1-alpha.1227").is_ok(),
                "2.0.1-alpha.1227 is valid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha+beta").is_ok(),
                "1.0.0-alpha+beta is valid"
            );
            assert!(
                SemVer::try_from("1.2.3----RC-SNAPSHOT.12.9.1--.12+788").is_ok(),
                "1.2.3----RC-SNAPSHOT.12.9.1--.12+788 is valid"
            );
            assert!(
                SemVer::try_from("1.2.3----R-S.12.9.1--.12+meta").is_ok(),
                "1.2.3----R-S.12.9.1--.12+meta is valid"
            );
            assert!(
                SemVer::try_from("1.2.3----RC-SNAPSHOT.12.9.1--.12").is_ok(),
                "1.2.3----RC-SNAPSHOT.12.9.1--.12 is valid"
            );
            assert!(
                SemVer::try_from("1.0.0+0.build.1-rc.10000aaa-kk-0.1").is_ok(),
                "1.0.0+0.build.1-rc.10000aaa-kk-0.1 is valid"
            );
            // 99999999999999999999999 is too big to fit in usize. I don't think it is interesting to use u128.
            // assert!(SemVer::try_from("99999999999999999999999.999999999999999999.99999999999999999").is_ok(), "99999999999999999999999.999999999999999999.99999999999999999 is valid");
            assert!(
                SemVer::try_from("1.0.0-0A.is.legal").is_ok(),
                "1.0.0-0A.is.legal is valid"
            );
        }

        #[test]
        fn invalid() {
            assert!(SemVer::try_from("1").is_err(), "1 is invalid");
            assert!(SemVer::try_from("1.2").is_err(), "1.2 is invalid");
            assert!(
                SemVer::try_from("1.2.3-0123").is_err(),
                "1.2.3-0123 is invalid"
            );
            assert!(
                SemVer::try_from("1.2.3-0123.0123").is_err(),
                "1.2.3-0123.0123 is invalid"
            );
            assert!(
                SemVer::try_from("1.1.2+.123").is_err(),
                "1.1.2+.123 is invalid"
            );
            assert!(SemVer::try_from("+invalid").is_err(), "+invalid is invalid");
            assert!(SemVer::try_from("-invalid").is_err(), "-invalid is invalid");
            assert!(
                SemVer::try_from("-invalid+invalid").is_err(),
                "-invalid+invalid is invalid"
            );
            assert!(
                SemVer::try_from("-invalid.01").is_err(),
                "-invalid.01 is invalid"
            );
            assert!(SemVer::try_from("alpha").is_err(), "alpha is invalid");
            assert!(
                SemVer::try_from("alpha.beta").is_err(),
                "alpha.beta is invalid"
            );
            assert!(
                SemVer::try_from("alpha.beta.1").is_err(),
                "alpha.beta.1 is invalid"
            );
            assert!(SemVer::try_from("alpha.1").is_err(), "alpha.1 is invalid");
            assert!(
                SemVer::try_from("alpha+beta").is_err(),
                "alpha+beta is invalid"
            );
            assert!(
                SemVer::try_from("alpha_beta").is_err(),
                "alpha_beta is invalid"
            );
            assert!(SemVer::try_from("alpha.").is_err(), "alpha. is invalid");
            assert!(SemVer::try_from("alpha..").is_err(), "alpha.. is invalid");
            assert!(SemVer::try_from("beta").is_err(), "beta is invalid");
            assert!(
                SemVer::try_from("1.0.0-alpha_beta").is_err(),
                "1.0.0-alpha_beta is invalid"
            );
            assert!(SemVer::try_from("-alpha.").is_err(), "-alpha. is invalid");
            assert!(
                SemVer::try_from("1.0.0-alpha..").is_err(),
                "1.0.0-alpha.. is invalid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha..1").is_err(),
                "1.0.0-alpha..1 is invalid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha...1").is_err(),
                "1.0.0-alpha...1 is invalid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha....1").is_err(),
                "1.0.0-alpha....1 is invalid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha.....1").is_err(),
                "1.0.0-alpha.....1 is invalid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha......1").is_err(),
                "1.0.0-alpha......1 is invalid"
            );
            assert!(
                SemVer::try_from("1.0.0-alpha.......1").is_err(),
                "1.0.0-alpha.......1 is invalid"
            );
            assert!(SemVer::try_from("01.1.1").is_err(), "01.1.1 is invalid");
            assert!(SemVer::try_from("1.01.1").is_err(), "1.01.1 is invalid");
            assert!(SemVer::try_from("1.1.01").is_err(), "1.1.01 is invalid");
            assert!(SemVer::try_from("1.2").is_err(), "1.2 is invalid");
            assert!(
                SemVer::try_from("1.2.3.DEV").is_err(),
                "1.2.3.DEV is invalid"
            );
            assert!(
                SemVer::try_from("1.2-SNAPSHOT").is_err(),
                "1.2-SNAPSHOT is invalid"
            );
            assert!(
                SemVer::try_from("1.2.31.2.3----RC-SNAPSHOT.12.09.1--..12+788").is_err(),
                "1.2.31.2.3----RC-SNAPSHOT.12.09.1--..12+788 is invalid"
            );
            assert!(
                SemVer::try_from("1.2-RC-SNAPSHOT").is_err(),
                "1.2-RC-SNAPSHOT is invalid"
            );
            assert!(
                SemVer::try_from("-1.0.3-gamma+b7718").is_err(),
                "-1.0.3-gamma+b7718 is invalid"
            );
            assert!(
                SemVer::try_from("+justmeta").is_err(),
                "+justmeta is invalid"
            );
            assert!(
                SemVer::try_from("9.8.7+meta+meta").is_err(),
                "9.8.7+meta+meta is invalid"
            );
            assert!(
                SemVer::try_from("9.8.7-whatever+meta+meta").is_err(),
                "9.8.7-whatever+meta+meta is invalid"
            );
            assert!(SemVer::try_from("99999999999999999999999.999999999999999999.99999999999999999----RC-SNAPSHOT.12.09.1--------------------------------..12").is_err(), "99999999999999999999999.999999999999999999.99999999999999999----RC-SNAPSHOT.12.09.1--------------------------------..12 is invalid");
        }
    }
}
