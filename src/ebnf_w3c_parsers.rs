/// W3C XML Style EBNF Syntax parser
/// Source https://www.w3.org/TR/REC-xml/#sec-notation
///
/// Self described W3C XML style EBNF syntax:
/// Grammar              ::= Production*
/// Production           ::= Name '::=' Expression
/// Expression           ::= DelimitedExp | UndelimietedExp
/// DelimitedExp         ::= ('(' UndelimitedExp ')') Repetition
/// UndelimitedExp       ::= (Term Repetition) | Difference | Choice | Sequence
/// Sequence             ::= (DelimitedExp | TermExp) Whitespace* ((DelimitedExp | Choice | TermExp) Whitespace*)+
/// Choice               ::= (DelimitedExp | TermExp) Whitespace* ('|' Whitespace* (DelimitedExp | Sequence | TermExp))+
/// Difference           ::= (DelimitedExp | TermExp) Whitespace* '-' Whitespace* (DelimitedExp | TermExp)
/// TermExp              ::= Term Repetition
/// Repetition           ::= ('?' | '*' | '+')?
/// Term                 ::= Name | StringLiteral | CharCode | CharClass
/// Name                 ::= NameStartChar NameChar*
/// NameStartChar        ::= [A-Z] | "_" | [a-z] | [#xC0-#xD6] | [#xD8-#xF6] | [#xF8-#x2FF] | [#x370-#x37D]
///                        | [#x37F-#x1FFF] | [#x200C-#x200D] | [#x2070-#x218F] | [#x2C00-#x2FEF] | [#x3001-#xD7FF]
///                        | [#xF900-#xFDCF] | [#xFDF0-#xFFFD] | [#x10000-#xEFFFF]
/// NameChar             ::= NameStartChar | "." | [0-9] | #xB7 | [#x0300-#x036F] | [#x203F-#x2040]
/// StringLiteral        ::= '"' [^"]* '"' | "'" [^']* "'"
/// CharCode             ::= '#x' [0-9a-fA-F]+
/// CharClass            ::= '[' '^'? ( Char | CharCode | CharRange | CharCodeRange )+ ']'
/// Char                 ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]
/// CharRange            ::= Char '-' ( Char - ']' )
/// CharCodeRange        ::= CharCode '-' CharCode
/// Whitespace           ::= Space | Comment
/// Space                ::= #x9 | #xA | #xD | #x20
/// Comment              ::= '/*' ( [^*] | '*'+ [^*/] )* '*'* '*/'
use nom::IResult;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Repetition {
    None,
    NoneOrOne,
    NoneOrMore,
    OneOrMore,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    Terminal {
        literal: String,
    },
    TerminalClass {
        invert: bool,
        ranges: Vec<(char, char)>,
    },
    NonTerminal {
        name: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expression {
    Term {
        term: Term,
        rep: Repetition,
    },
    Difference {
        // Minuend - Suptrahend = Difference
        min: Box<Expression>,
        sub: Box<Expression>,
        rep: Repetition,
    },
    Sequence {
        exprs: Vec<Expression>,
        rep: Repetition,
    },
    Choice {
        exprs: Vec<Expression>,
        rep: Repetition,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Production {
    lhs: Term,
    rhs: Expression,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Grammar {
    productions: Vec<Production>,
}

pub fn range(start_char: char, end_char: char) -> impl Fn(&str) -> IResult<&str, char> {
    use nom::{error::ErrorKind, Err, Needed};
    move |i: &str| match (i)
        .chars()
        .next()
        .map(|c| (c, (c >= start_char) && (c <= end_char)))
    {
        None => Err(Err::Incomplete(Needed::Size(1))),
        Some((_, false)) => Err(Err::Error((i, ErrorKind::Char))),
        Some((c, true)) => Ok((&i[c.len_utf8()..], c)),
    }
}

// Comment ::= '/*' ( [^*] | '*'+ [^*/] )* '*'* '*/'
pub fn space(i: &str) -> IResult<&str, &str> {
    use nom::branch::alt;
    use nom::bytes::streaming::tag;
    alt((tag("\u{9}"), tag("\u{a}"), tag("\u{d}"), tag("\u{20}")))(i)
}

// Space ::= #x9 | #xA | #xD | #x20
pub fn comment(i: &str) -> IResult<&str, &str> {
    use nom::bytes::streaming::{tag, take_until};
    let (i, _) = tag("/*")(i)?;
    let (i, c) = take_until("*/")(i)?;
    let (i, _) = tag("*/")(i)?;
    return Ok((i, c));
}

// Whitespace  ::= Space | Comment
pub fn whitespace(i: &str) -> IResult<&str, &str> {
    use nom::branch::alt;
    alt((space, comment))(i)
}

// Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]
pub fn character(i: &str) -> IResult<&str, char> {
    use nom::character::streaming::none_of;
    let (i, c) = none_of("]")(i)?;
    Ok((i, c))
}

// CharRange ::= Char '-' ( Char - ']' )
pub fn char_range(i: &str) -> IResult<&str, (char, char)> {
    use nom::character::streaming::{anychar, char, none_of};
    let (i, start_char) = anychar(i)?;
    let (i, _) = char('-')(i)?;
    let (i, end_char) = none_of("-")(i)?;
    Ok((i, (start_char, end_char)))
}

// CharCode ::= '#x' [0-9a-fA-F]+
pub fn char_code(i: &str) -> IResult<&str, char> {
    use nom::bytes::streaming::tag;
    use nom::character::streaming::hex_digit1;
    use nom::{error::ErrorKind, Err};
    use std::convert::TryFrom;
    let (i, _) = tag("#x")(i)?;
    let (i, num) = hex_digit1(i)?;
    match u32::from_str_radix(num, 16) {
        Err(_) => Err(Err::Error((i, ErrorKind::HexDigit))),
        Ok(val) => match char::try_from(val) {
            Err(_) => Err(Err::Error((i, ErrorKind::Char))),
            Ok(c) => Ok((i, c)),
        },
    }
}

// CharCodeRange ::= CharCode '-' CharCode
pub fn char_code_range(i: &str) -> IResult<&str, (char, char)> {
    use nom::character::streaming;
    let (i, start_char) = char_code(i)?;
    let (i, _) = streaming::char('-')(i)?;
    let (i, end_char) = char_code(i)?;
    Ok((i, (start_char, end_char)))
}

// CharClass ::= '[' '^'? ( Char | CharCode | CharRange | CharCodeRange )+ ']'
pub fn char_class(i: &str) -> IResult<&str, (bool, Vec<(char, char)>)> {
    use nom::Err;
    use nom::{
        branch::alt,
        bytes::streaming::tag,
        character::streaming,
        combinator::{complete, map},
        multi::many1,
    };
    let (i, _) = tag("[")(i)?;
    let (i, invert) = match streaming::char('^')(i) {
        Ok((i, _)) => (i, true),
        Err(e) => match e {
            Err::Error(_) => (i, false),
            _ => return Err(e),
        },
    };
    let (i, o) = many1(alt((
        complete(char_code_range),
        complete(char_range),
        map(complete(char_code), |c: char| (c, c)),
        map(complete(character), |c: char| (c, c)),
    )))(i)?;
    let (i, _) = tag("]")(i)?;
    Ok((i, (invert, o)))
}

// StringLiteral ::= '"' [^"]* '"' | "'" [^']* "'"
pub fn string_literal(i: &str) -> IResult<&str, String> {
    use nom::branch::alt;
    use nom::bytes::streaming::{is_not, tag};
    let (i, delim) = alt((tag("\""), tag("'")))(i)?;
    let (i, o) = is_not(delim)(i)?;
    let (i, _) = tag(delim)(i)?;
    Ok((i, o.to_owned()))
}

// NameStartChar ::= [A-Z] | "_" | [a-z] | [#xC0-#xD6] | [#xD8-#xF6] | [#xF8-#x2FF] | [#x370-#x37D]
//                 | [#x37F-#x1FFF] | [#x200C-#x200D] | [#x2070-#x218F] | [#x2C00-#x2FEF] | [#x3001-#xD7FF]
//                 | [#xF900-#xFDCF] | [#xFDF0-#xFFFD] | [#x10000-#xEFFFF]
pub fn name_start_char(i: &str) -> IResult<&str, char> {
    use nom::branch::alt;
    use nom::character::streaming::char;
    alt((
        range('A', 'Z'),
        char('_'),
        range('a', 'z'),
        range('\u{c0}', '\u{D6}'),
        range('\u{d8}', '\u{f6}'),
        range('\u{f8}', '\u{2ff}'),
        range('\u{370}', '\u{37d}'),
        range('\u{37f}', '\u{1fff}'),
        range('\u{200c}', '\u{200d}'),
        range('\u{2070}', '\u{218f}'),
        range('\u{2c00}', '\u{2fef}'),
        range('\u{3001}', '\u{d7ff}'),
        range('\u{f900}', '\u{fdcf}'),
        range('\u{fdf0}', '\u{fffd}'),
        range('\u{10000}', '\u{effff}'),
    ))(i)
}

// NameChar ::= NameStartChar | "." | [0-9] | #xB7 | [#x0300-#x036F] | [#x203F-#x2040]
pub fn name_char(i: &str) -> IResult<&str, char> {
    use nom::branch::alt;
    use nom::character::streaming::char;
    alt((
        name_start_char,
        char('.'),
        range('0', '9'),
        char('\u{b7}'),
        range('\u{300}', '\u{36f}'),
        range('\u{203f}', '\u{2040}'),
    ))(i)
}

// Name ::= NameStartChar NameChar*
pub fn name(i: &str) -> IResult<&str, String> {
    use nom::multi::fold_many0;
    let (i, s) = name_start_char(i)?;
    let (i, o) = fold_many0(name_char, s.to_string(), |mut acc: String, item| {
        acc.push(item);
        acc
    })(i)?;
    Ok((i, o))
}

// Term ::= Name | StringLiteral | CharCode | CharClass
pub fn term(i: &str) -> IResult<&str, Term> {
    use nom::branch::alt;
    use nom::combinator::map;
    alt((
        map(name, |s: String| Term::NonTerminal { name: s }),
        map(string_literal, |s: String| Term::Terminal { literal: s }),
        map(char_code, |c: char| Term::Terminal {
            literal: c.to_string(),
        }),
        map(char_class, |t: (bool, Vec<(char, char)>)| {
            Term::TerminalClass {
                invert: t.0,
                ranges: t.1,
            }
        }),
    ))(i)
}

// Repetition ::= ('?' | '*' | '+')?
pub fn repetition(i: &str) -> IResult<&str, Repetition> {
    use nom::branch::alt;
    use nom::character::streaming::char;
    use nom::combinator::{complete, map, opt};
    map(
        opt(complete(alt((char('?'), char('*'), char('+'))))),
        |c: Option<char>| match c {
            Some(c) => match c {
                '?' => Repetition::NoneOrOne,
                '*' => Repetition::NoneOrMore,
                '+' => Repetition::OneOrMore,
                _ => panic!("Invalid repetition character"),
            },
            None => Repetition::None,
        },
    )(i)
}

// TermExp ::= Term Repetition
pub fn term_exp(i: &str) -> IResult<&str, Expression> {
    use nom::bytes::streaming::tag;
    use nom::combinator::{complete, map, not, peek};
    use nom::multi::many0_count;
    use nom::sequence::{terminated, tuple};
    terminated(
        map(tuple((term, repetition)), |t: (Term, Repetition)| {
            Expression::Term {
                term: t.0,
                rep: t.1,
            }
        }),
        peek(not(complete(tuple((many0_count(whitespace), tag("::=")))))),
    )(i)
}

// Difference ::= (DelimitedExp | TermExp) Whitespace* '-' Whitespace* (DelimitedExp | Term)
pub fn difference(i: &str) -> IResult<&str, Expression> {
    use nom::branch::alt;
    use nom::character::streaming::char;
    use nom::combinator::{complete, map};
    use nom::multi::many0_count;
    use nom::sequence::tuple;
    map(
        tuple((
            alt((delimited_exp, term_exp)),
            many0_count(whitespace),
            char('-'),
            many0_count(whitespace),
            alt((complete(delimited_exp), complete(term_exp))),
        )),
        |t: (Expression, usize, char, usize, Expression)| Expression::Difference {
            min: Box::new(t.0),
            sub: Box::new(t.4),
            rep: Repetition::None,
        },
    )(i)
}

// Choice ::= (DelimitedExp | TermExp) Whitespace* ('|' Whitespace* (DelimitedExp | Sequence | TermExp))+
pub fn choice(i: &str) -> IResult<&str, Expression> {
    use nom::branch::alt;
    use nom::character::streaming::char;
    use nom::combinator::complete;
    use nom::multi::{many0_count, separated_nonempty_list};
    use nom::sequence::{terminated, tuple};
    let mut exprs: Vec<Expression> = vec![];
    let (i, first) = terminated(
        alt((delimited_exp, term_exp)),
        tuple((many0_count(whitespace), char('|'), many0_count(whitespace))),
    )(i)?;
    exprs.push(first);
    let (i, remaining) = separated_nonempty_list(
        complete(tuple((
            many0_count(whitespace),
            char('|'),
            many0_count(whitespace),
        ))),
        alt((
            complete(delimited_exp),
            complete(sequence),
            complete(term_exp),
        )),
    )(i)?;
    exprs.extend(remaining);
    Ok((
        i,
        Expression::Choice {
            exprs,
            rep: Repetition::None,
        },
    ))
}

// Sequence ::= (DelemitedExp | TermExp) Whitespace* ((DelimitedExp | Choice | TermExp) Whitespace*)*
pub fn sequence(i: &str) -> IResult<&str, Expression> {
    use nom::branch::alt;
    use nom::combinator::complete;
    use nom::multi::{many1_count, separated_nonempty_list};
    use nom::sequence::terminated;
    let mut exprs: Vec<Expression> = vec![];
    let (i, first) = terminated(alt((delimited_exp, term_exp)), many1_count(whitespace))(i)?;
    exprs.push(first);
    let (i, remaining) = separated_nonempty_list(
        complete(many1_count(whitespace)),
        alt((
            complete(delimited_exp),
            complete(choice),
            complete(term_exp),
        )),
    )(i)?;
    exprs.extend(remaining);
    Ok((
        i,
        Expression::Sequence {
            exprs,
            rep: Repetition::None,
        },
    ))
}

// UndelimitedExp ::= (Term Repetition) | Difference | Choice | Sequence
pub fn undelimited_exp(i: &str) -> IResult<&str, Expression> {
    use nom::branch::alt;
    use nom::combinator::{complete, map};
    use nom::sequence::tuple;
    alt((
        complete(difference),
        complete(choice),
        complete(sequence),
        complete(map(tuple((term, repetition)), |t: (Term, Repetition)| {
            Expression::Term {
                term: t.0,
                rep: t.1,
            }
        })),
    ))(i)
}

// DelimitedExp ::= ('(' UndelimitedExp ')') Repetition
pub fn delimited_exp(i: &str) -> IResult<&str, Expression> {
    use nom::character::streaming::char;
    use nom::combinator::map;
    use nom::multi::many0_count;
    use nom::sequence::tuple;
    map(
        tuple((
            char('('),
            many0_count(whitespace),
            undelimited_exp,
            many0_count(whitespace),
            char(')'),
            repetition,
        )),
        |t: (char, usize, Expression, usize, char, Repetition)| match t.2 {
            Expression::Term { term, rep } => match (rep.clone(), t.5.clone()) {
                (Repetition::None, Repetition::None) => Expression::Term {
                    term,
                    rep: Repetition::None,
                },
                (Repetition::None, _) => Expression::Term { term, rep: t.5 },
                (_, Repetition::None) => Expression::Term { term, rep },
                (_, _) => Expression::Sequence {
                    exprs: vec![Expression::Term { term, rep }],
                    rep: t.5,
                },
            },
            Expression::Difference { min, sub, rep: _ } => {
                Expression::Difference { min, sub, rep: t.5 }
            }
            Expression::Sequence { exprs, rep: _ } => Expression::Sequence { exprs, rep: t.5 },
            Expression::Choice { exprs, rep: _ } => Expression::Choice { exprs, rep: t.5 },
        },
    )(i)
}

// Expression ::= DelimitedExp | UndelimietedExp
pub fn expression(i: &str) -> IResult<&str, Expression> {
    use nom::branch::alt;
    use nom::bytes::streaming::tag;
    use nom::combinator::{complete, not, peek};
    use nom::multi::many0_count;
    use nom::sequence::{terminated, tuple};
    terminated(
        alt((undelimited_exp, delimited_exp)),
        not(complete(peek(tuple((many0_count(whitespace), tag("::=")))))),
    )(i)
}

// Production ::= Name '::=' Expression
pub fn production(i: &str) -> IResult<&str, Production> {
    use nom::bytes::streaming::tag;
    use nom::multi::many0_count;
    let (i, _) = many0_count(whitespace)(i)?;
    let (i, lhs) = term(i)?;
    let (i, _) = many0_count(whitespace)(i)?;
    let (i, _) = tag("::=")(i)?;
    let (i, _) = many0_count(whitespace)(i)?;
    let (i, rhs) = expression(i)?;
    Ok((i, Production { lhs, rhs }))
}

// Grammar ::= Production*
pub fn grammar(i: &str) -> IResult<&str, Grammar> {
    use nom::combinator::complete;
    use nom::multi::{many0_count, separated_list};
    let (i, productions) = separated_list(complete(many0_count(whitespace)), production)(i)?;
    Ok((i, Grammar { productions }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::{error::ErrorKind, Err, Needed};

    #[test]
    fn range_test() {
        assert_eq!(range('a', 'z')("b"), Ok(("", 'b')));
        assert_eq!(
            range('a', 'z')("A"),
            Err(Err::Error(("A", ErrorKind::Char)))
        );
    }

    #[test]
    fn space_match() {
        assert_eq!(space("  test"), Ok((" test", " ")));
        assert_eq!(space("\t test"), Ok((" test", "\t")));
        assert_eq!(space("\n test"), Ok((" test", "\n")));
        assert_eq!(space("\r test"), Ok((" test", "\r")));
        assert_eq!(space("test"), Err(Err::Error(("test", ErrorKind::Tag))));
    }

    #[test]
    fn comment_match() {
        assert_eq!(
            comment("/* test ** comment **/"),
            Ok(("", " test ** comment *"))
        );
        assert_eq!(
            comment("/* test ** comment"),
            Err(Err::Incomplete(Needed::Size(2)))
        );
    }

    #[test]
    fn whitespace_match() {
        assert_eq!(whitespace("  test"), Ok((" test", " ")));
        assert_eq!(
            whitespace("/* test ** comment **/"),
            Ok(("", " test ** comment *"))
        );
    }

    #[test]
    fn char_match() {
        assert_eq!(character("abcd"), Ok(("bcd", 'a')));
        assert_eq!(character("\u{2211}abcd"), Ok(("abcd", '\u{2211}')));
    }

    #[test]
    fn char_range_match() {
        assert_eq!(char_range("a-zd"), Ok(("d", ('a', 'z'))));
        assert_eq!(char_range("\u{0}-\u{2211}"), Ok(("", ('\0', '\u{2211}'))));
        assert_eq!(char_range("a--"), Err(Err::Error(("-", ErrorKind::NoneOf))));
    }

    #[test]
    fn char_code_match() {
        assert_eq!(char_code("#x0000 test"), Ok((" test", '\0')));
        assert_eq!(char_code("#x0B87test"), Ok(("test", '\u{0b87}')));
        assert_eq!(
            char_code("#x0B87#x0b86test"),
            Ok(("#x0b86test", '\u{0b87}'))
        );
        assert_eq!(
            char_code("#xtest"),
            Err(Err::Error(("test", ErrorKind::HexDigit)))
        );
    }

    #[test]
    fn char_code_range_match() {
        assert_eq!(
            char_code_range("#x0000-#xFFFF test"),
            Ok((" test", ('\0', '\u{ffff}')))
        );
        assert_eq!(
            char_code_range("#x04D2-#x0b87test"),
            Ok(("test", ('\u{04D2}', '\u{0b87}')))
        );
        assert_eq!(
            char_code_range("#x04D2-#x0b87#x0000test"),
            Ok(("#x0000test", ('\u{04D2}', '\u{0b87}')))
        );
        assert_eq!(
            char_code_range("#xdead=#xbeef"),
            Err(Err::Error(("=#xbeef", ErrorKind::Char)))
        );
        assert_eq!(
            char_code_range("#x04d2-#xtest"),
            Err(Err::Error(("test", ErrorKind::HexDigit)))
        );
    }

    #[test]
    fn char_class_match() {
        assert_eq!(
            char_class("[^abcd]"),
            Ok((
                "",
                (true, vec![('a', 'a'), ('b', 'b'), ('c', 'c'), ('d', 'd')])
            ))
        );
        assert_eq!(
            char_class("[a-zA-Z]"),
            Ok(("", (false, vec![('a', 'z'), ('A', 'Z')])))
        );
        assert_eq!(
            char_class("[\u{0391}-Ϋ]"),
            Ok(("", (false, vec![('Α', 'Ϋ')])))
        );
        assert_eq!(
            char_class("[^#x0061-#x007a#x41-#x5A]"),
            Ok(("", (true, vec![('a', 'z'), ('A', 'Z')])))
        );
        assert_eq!(
            char_class("[a-z#x41-#x5A]"),
            Ok(("", (false, vec![('a', 'z'), ('A', 'Z')])))
        );
        assert_eq!(
            char_class("[^a-z#x41-#x5A#x0xyz]"),
            Ok((
                "",
                (
                    true,
                    vec![
                        ('a', 'z'),
                        ('A', 'Z'),
                        ('\0', '\0'),
                        ('x', 'x'),
                        ('y', 'y'),
                        ('z', 'z')
                    ]
                )
            ))
        );
    }

    #[test]
    fn string_literal_match() {
        assert_eq!(
            string_literal("'Hello WorldΘ'"),
            Ok(("", String::from("Hello WorldΘ")))
        );
        assert_eq!(
            string_literal("\"Hello World\""),
            Ok(("", String::from("Hello World")))
        );
        assert_eq!(
            string_literal("\"'Hello World\"'"),
            Ok(("'", String::from("'Hello World")))
        );
        assert_eq!(
            string_literal(" \"Hello World\""),
            Err(Err::Error((" \"Hello World\"", ErrorKind::Tag)))
        );
        assert_eq!(
            string_literal("'Hello Worl"),
            Err(Err::Incomplete(Needed::Size(1)))
        );
    }

    #[test]
    fn name_start_char_match() {
        assert_eq!(name_start_char("Abcd"), Ok(("bcd", 'A')));
        assert_eq!(name_start_char("\u{f8}"), Ok(("", '\u{f8}')));
        assert_eq!(
            name_start_char("0Abcd"),
            Err(Err::Error(("0Abcd", ErrorKind::Char)))
        );
    }

    #[test]
    fn name_char_match() {
        assert_eq!(name_char("Abcd"), Ok(("bcd", 'A')));
        assert_eq!(name_char("\u{f8}"), Ok(("", '\u{f8}')));
        assert_eq!(name_char("0Abcd"), Ok(("Abcd", '0')));
        assert_eq!(name_char("\n"), Err(Err::Error(("\n", ErrorKind::Char))));
    }

    #[test]
    fn name_match() {
        assert_eq!(name("Abcd "), Ok((" ", String::from("Abcd"))));
        assert_eq!(name("Abcd efgh"), Ok((" efgh", String::from("Abcd"))));
        assert_eq!(name("-Abcd"), Err(Err::Error(("-Abcd", ErrorKind::Char))));
    }

    #[test]
    fn term_match() {
        assert_eq!(
            term("Test \"TestLiteral\" #x1fa [a-z#xA-#x1f]"),
            Ok((
                " \"TestLiteral\" #x1fa [a-z#xA-#x1f]",
                Term::NonTerminal {
                    name: String::from("Test")
                }
            ))
        );
        assert_eq!(
            term("\"Test Literal\" #x1fa [a-z#xA-#x1f] Test"),
            Ok((
                " #x1fa [a-z#xA-#x1f] Test",
                Term::Terminal {
                    literal: String::from("Test Literal")
                }
            ))
        );
        assert_eq!(
            term("#x1fa [a-z#xA-#x1f] Test \"Test Literal\""),
            Ok((
                " [a-z#xA-#x1f] Test \"Test Literal\"",
                Term::Terminal {
                    literal: String::from("\u{1fa}")
                }
            ))
        );
        assert_eq!(
            term("[a-z#xA-#x1f] Test \"Test Literal\" #x1fa"),
            Ok((
                " Test \"Test Literal\" #x1fa",
                Term::TerminalClass {
                    invert: false,
                    ranges: vec![('a', 'z'), ('\u{a}', '\u{1f}')]
                }
            ))
        );
    }

    #[test]
    fn repetition_match() {
        assert_eq!(repetition("*"), Ok(("", Repetition::NoneOrMore)));
        assert_eq!(repetition("+"), Ok(("", Repetition::OneOrMore)));
        assert_eq!(repetition("?"), Ok(("", Repetition::NoneOrOne)));
        assert_eq!(repetition("a"), Ok(("a", Repetition::None)));
    }

    #[test]
    fn difference_match() {
        assert_eq!(
            difference("Test1 -'Test2'+"),
            Ok((
                "",
                Expression::Difference {
                    min: Box::new(Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test1")
                        },
                        rep: Repetition::None
                    }),
                    sub: Box::new(Expression::Term {
                        term: Term::Terminal {
                            literal: String::from("Test2")
                        },
                        rep: Repetition::OneOrMore
                    }),
                    rep: Repetition::None,
                }
            ))
        );
        assert_eq!(
            difference("Test1 - ('Test2'+ | Test3)"),
            Ok((
                "",
                Expression::Difference {
                    min: Box::new(Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test1")
                        },
                        rep: Repetition::None
                    }),
                    sub: Box::new(Expression::Choice {
                        exprs: vec![
                            Expression::Term {
                                term: Term::Terminal {
                                    literal: String::from("Test2")
                                },
                                rep: Repetition::OneOrMore
                            },
                            Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }
                        ],
                        rep: Repetition::None
                    }),
                    rep: Repetition::None
                }
            ))
        );
    }

    #[test]
    fn choice_match() {
        assert_eq!(
            choice("(Test1+) | Test2* | (Test3)? | 'Test4'"),
            Ok((
                "",
                Expression::Choice {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::OneOrMore
                        },
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test2")
                            },
                            rep: Repetition::NoneOrMore
                        },
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test3")
                            },
                            rep: Repetition::NoneOrOne
                        },
                        Expression::Term {
                            term: Term::Terminal {
                                literal: String::from("Test4")
                            },
                            rep: Repetition::None
                        },
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            choice("Test1 | (Test2 - Test3)"),
            Ok((
                "",
                Expression::Choice {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::None
                        },
                        Expression::Difference {
                            min: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test2")
                                },
                                rep: Repetition::None
                            }),
                            sub: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }),
                            rep: Repetition::None
                        }
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            choice("(Test1 Test2)+ | (Test3 - Test4)"),
            Ok((
                "",
                Expression::Choice {
                    exprs: vec![
                        Expression::Sequence {
                            exprs: vec![
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test1")
                                    },
                                    rep: Repetition::None
                                },
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test2")
                                    },
                                    rep: Repetition::None
                                }
                            ],
                            rep: Repetition::OneOrMore
                        },
                        Expression::Difference {
                            min: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }),
                            sub: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test4")
                                },
                                rep: Repetition::None
                            }),
                            rep: Repetition::None
                        }
                    ],
                    rep: Repetition::None
                }
            ))
        );
    }

    #[test]
    fn sequence_match() {
        assert_eq!(
            sequence("(Test1+) Test2* (Test3)? 'Test4'"),
            Ok((
                "",
                Expression::Sequence {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::OneOrMore
                        },
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test2")
                            },
                            rep: Repetition::NoneOrMore
                        },
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test3")
                            },
                            rep: Repetition::NoneOrOne
                        },
                        Expression::Term {
                            term: Term::Terminal {
                                literal: String::from("Test4")
                            },
                            rep: Repetition::None
                        },
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            sequence("Test1 (Test2 - Test3)"),
            Ok((
                "",
                Expression::Sequence {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::None
                        },
                        Expression::Difference {
                            min: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test2")
                                },
                                rep: Repetition::None
                            }),
                            sub: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }),
                            rep: Repetition::None
                        }
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            sequence("(Test1 | Test2)+ (Test3 - Test4)"),
            Ok((
                "",
                Expression::Sequence {
                    exprs: vec![
                        Expression::Choice {
                            exprs: vec![
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test1")
                                    },
                                    rep: Repetition::None
                                },
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test2")
                                    },
                                    rep: Repetition::None
                                },
                            ],
                            rep: Repetition::OneOrMore
                        },
                        Expression::Difference {
                            min: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }),
                            sub: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test4")
                                },
                                rep: Repetition::None
                            }),
                            rep: Repetition::None
                        }
                    ],
                    rep: Repetition::None
                }
            ))
        );
    }

    #[test]
    fn expression_match() {
        assert_eq!(
            expression("Test+"),
            Ok((
                "",
                Expression::Term {
                    term: Term::NonTerminal {
                        name: String::from("Test")
                    },
                    rep: Repetition::OneOrMore
                }
            ))
        );
        assert_eq!(
            expression("(Test)+"),
            Ok((
                "",
                Expression::Term {
                    term: Term::NonTerminal {
                        name: String::from("Test")
                    },
                    rep: Repetition::OneOrMore
                }
            ))
        );
        assert_eq!(
            expression("(Test*)+"),
            Ok((
                "",
                Expression::Sequence {
                    exprs: vec![Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test")
                        },
                        rep: Repetition::NoneOrMore
                    }],
                    rep: Repetition::OneOrMore
                }
            ))
        );
        assert_eq!(
            expression("Test1 - 'Test2'+"),
            Ok((
                "",
                Expression::Difference {
                    min: Box::new(Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test1")
                        },
                        rep: Repetition::None
                    }),
                    sub: Box::new(Expression::Term {
                        term: Term::Terminal {
                            literal: String::from("Test2")
                        },
                        rep: Repetition::OneOrMore
                    }),
                    rep: Repetition::None,
                }
            ))
        );
        assert_eq!(
            expression("(Test1 - 'Test2'+)"),
            Ok((
                "",
                Expression::Difference {
                    min: Box::new(Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test1")
                        },
                        rep: Repetition::None
                    }),
                    sub: Box::new(Expression::Term {
                        term: Term::Terminal {
                            literal: String::from("Test2")
                        },
                        rep: Repetition::OneOrMore
                    }),
                    rep: Repetition::None,
                }
            ))
        );
        assert_eq!(
            expression("((Test1?) - 'Test2'+)*"),
            Ok((
                "",
                Expression::Difference {
                    min: Box::new(Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test1")
                        },
                        rep: Repetition::NoneOrOne
                    }),
                    sub: Box::new(Expression::Term {
                        term: Term::Terminal {
                            literal: String::from("Test2")
                        },
                        rep: Repetition::OneOrMore
                    }),
                    rep: Repetition::NoneOrMore,
                }
            ))
        );
        assert_eq!(
            expression("(Test1+) | Test2* | (Test3)? | 'Test4'"),
            Ok((
                "",
                Expression::Choice {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::OneOrMore
                        },
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test2")
                            },
                            rep: Repetition::NoneOrMore
                        },
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test3")
                            },
                            rep: Repetition::NoneOrOne
                        },
                        Expression::Term {
                            term: Term::Terminal {
                                literal: String::from("Test4")
                            },
                            rep: Repetition::None
                        },
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            expression("Test1 | (Test2 - Test3)"),
            Ok((
                "",
                Expression::Choice {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::None
                        },
                        Expression::Difference {
                            min: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test2")
                                },
                                rep: Repetition::None
                            }),
                            sub: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }),
                            rep: Repetition::None
                        }
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            expression("(Test1 Test2)+ | (Test3 - Test4)"),
            Ok((
                "",
                Expression::Choice {
                    exprs: vec![
                        Expression::Sequence {
                            exprs: vec![
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test1")
                                    },
                                    rep: Repetition::None
                                },
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test2")
                                    },
                                    rep: Repetition::None
                                }
                            ],
                            rep: Repetition::OneOrMore
                        },
                        Expression::Difference {
                            min: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }),
                            sub: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test4")
                                },
                                rep: Repetition::None
                            }),
                            rep: Repetition::None
                        }
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            expression("(Test1 - ('Test2'+ | Test3)+)"),
            Ok((
                "",
                Expression::Difference {
                    min: Box::new(Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test1")
                        },
                        rep: Repetition::None
                    }),
                    sub: Box::new(Expression::Choice {
                        exprs: vec![
                            Expression::Term {
                                term: Term::Terminal {
                                    literal: String::from("Test2")
                                },
                                rep: Repetition::OneOrMore
                            },
                            Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }
                        ],
                        rep: Repetition::OneOrMore
                    }),
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            expression("(Test1+) Test2* (Test3)? 'Test4'"),
            Ok((
                "",
                Expression::Sequence {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::OneOrMore
                        },
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test2")
                            },
                            rep: Repetition::NoneOrMore
                        },
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test3")
                            },
                            rep: Repetition::NoneOrOne
                        },
                        Expression::Term {
                            term: Term::Terminal {
                                literal: String::from("Test4")
                            },
                            rep: Repetition::None
                        },
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            expression("Test1 (Test2 - Test3)"),
            Ok((
                "",
                Expression::Sequence {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::None
                        },
                        Expression::Difference {
                            min: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test2")
                                },
                                rep: Repetition::None
                            }),
                            sub: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }),
                            rep: Repetition::None
                        }
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            expression("(Test1 | Test2)+ (Test3 - Test4)"),
            Ok((
                "",
                Expression::Sequence {
                    exprs: vec![
                        Expression::Choice {
                            exprs: vec![
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test1")
                                    },
                                    rep: Repetition::None
                                },
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test2")
                                    },
                                    rep: Repetition::None
                                },
                            ],
                            rep: Repetition::OneOrMore
                        },
                        Expression::Difference {
                            min: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::None
                            }),
                            sub: Box::new(Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test4")
                                },
                                rep: Repetition::None
                            }),
                            rep: Repetition::None
                        }
                    ],
                    rep: Repetition::None
                }
            ))
        );
        assert_eq!(
            expression("Test1 | Test2+ (Test3 - Test4)"),
            Ok((
                "",
                Expression::Choice {
                    exprs: vec![
                        Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::None
                        },
                        Expression::Sequence {
                            exprs: vec![
                                Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test2")
                                    },
                                    rep: Repetition::OneOrMore
                                },
                                Expression::Difference {
                                    min: Box::new(Expression::Term {
                                        term: Term::NonTerminal {
                                            name: String::from("Test3")
                                        },
                                        rep: Repetition::None
                                    }),
                                    sub: Box::new(Expression::Term {
                                        term: Term::NonTerminal {
                                            name: String::from("Test4")
                                        },
                                        rep: Repetition::None
                                    }),
                                    rep: Repetition::None
                                }
                            ],
                            rep: Repetition::None
                        },
                    ],
                    rep: Repetition::None
                }
            ))
        );
    }

    #[test]
    fn production_match() {
        assert_eq!(
            production("Prod ::= Test+"),
            Ok((
                "",
                Production {
                    lhs: Term::NonTerminal {
                        name: String::from("Prod")
                    },
                    rhs: Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test")
                        },
                        rep: Repetition::OneOrMore
                    }
                }
            ))
        );
        assert_eq!(
            production("Prod ::= (Test)+"),
            Ok((
                "",
                Production {
                    lhs: Term::NonTerminal {
                        name: String::from("Prod")
                    },
                    rhs: Expression::Term {
                        term: Term::NonTerminal {
                            name: String::from("Test")
                        },
                        rep: Repetition::OneOrMore
                    }
                }
            ))
        );
        assert_eq!(
            production("Prod ::= (Test*)+"),
            Ok((
                "",
                Production {
                    lhs: Term::NonTerminal {
                        name: String::from("Prod")
                    },
                    rhs: Expression::Sequence {
                        exprs: vec![Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test")
                            },
                            rep: Repetition::NoneOrMore
                        }],
                        rep: Repetition::OneOrMore
                    }
                }
            ))
        );
        assert_eq!(
            production("Prod ::= Test1 - 'Test2'+"),
            Ok((
                "",
                Production {
                    lhs: Term::NonTerminal {
                        name: String::from("Prod")
                    },
                    rhs: Expression::Difference {
                        min: Box::new(Expression::Term {
                            term: Term::NonTerminal {
                                name: String::from("Test1")
                            },
                            rep: Repetition::None
                        }),
                        sub: Box::new(Expression::Term {
                            term: Term::Terminal {
                                literal: String::from("Test2")
                            },
                            rep: Repetition::OneOrMore
                        }),
                        rep: Repetition::None,
                    }
                }
            ))
        );
        assert_eq!(
            production("Prod::= (Test1+) | Test2* | (Test3)? | 'Test4'"),
            Ok((
                "",
                Production {
                    lhs: Term::NonTerminal {
                        name: String::from("Prod")
                    },
                    rhs: Expression::Choice {
                        exprs: vec![
                            Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test1")
                                },
                                rep: Repetition::OneOrMore
                            },
                            Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test2")
                                },
                                rep: Repetition::NoneOrMore
                            },
                            Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test3")
                                },
                                rep: Repetition::NoneOrOne
                            },
                            Expression::Term {
                                term: Term::Terminal {
                                    literal: String::from("Test4")
                                },
                                rep: Repetition::None
                            },
                        ],
                        rep: Repetition::None
                    }
                }
            ))
        );
        assert_eq!(
            production("Prod ::=Test1 | Test2+ (Test3 - Test4)"),
            Ok((
                "",
                Production {
                    lhs: Term::NonTerminal {
                        name: String::from("Prod")
                    },
                    rhs: Expression::Choice {
                        exprs: vec![
                            Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test1")
                                },
                                rep: Repetition::None
                            },
                            Expression::Sequence {
                                exprs: vec![
                                    Expression::Term {
                                        term: Term::NonTerminal {
                                            name: String::from("Test2")
                                        },
                                        rep: Repetition::OneOrMore
                                    },
                                    Expression::Difference {
                                        min: Box::new(Expression::Term {
                                            term: Term::NonTerminal {
                                                name: String::from("Test3")
                                            },
                                            rep: Repetition::None
                                        }),
                                        sub: Box::new(Expression::Term {
                                            term: Term::NonTerminal {
                                                name: String::from("Test4")
                                            },
                                            rep: Repetition::None
                                        }),
                                        rep: Repetition::None
                                    }
                                ],
                                rep: Repetition::None
                            },
                        ],
                        rep: Repetition::None
                    }
                }
            ))
        );
    }

    #[test]
    fn grammar_match() {
        assert_eq!(
            grammar(
                "
Prod1 ::= Test+
/*Test Comment*/
Prod2::= (Test1+) | Test2* | (Test3)? | 'Test4'
Prod3 ::=Test1 | Test2+ (Test3 - Test4)
Prod4 ::= Test1 /* Internal Comment Test */
          - 'Test2'+"
            ),
            Ok((
                "",
                Grammar {
                    productions: vec![
                        Production {
                            lhs: Term::NonTerminal {
                                name: String::from("Prod1")
                            },
                            rhs: Expression::Term {
                                term: Term::NonTerminal {
                                    name: String::from("Test")
                                },
                                rep: Repetition::OneOrMore
                            }
                        },
                        Production {
                            lhs: Term::NonTerminal {
                                name: String::from("Prod2")
                            },
                            rhs: Expression::Choice {
                                exprs: vec![
                                    Expression::Term {
                                        term: Term::NonTerminal {
                                            name: String::from("Test1")
                                        },
                                        rep: Repetition::OneOrMore
                                    },
                                    Expression::Term {
                                        term: Term::NonTerminal {
                                            name: String::from("Test2")
                                        },
                                        rep: Repetition::NoneOrMore
                                    },
                                    Expression::Term {
                                        term: Term::NonTerminal {
                                            name: String::from("Test3")
                                        },
                                        rep: Repetition::NoneOrOne
                                    },
                                    Expression::Term {
                                        term: Term::Terminal {
                                            literal: String::from("Test4")
                                        },
                                        rep: Repetition::None
                                    },
                                ],
                                rep: Repetition::None
                            }
                        },
                        Production {
                            lhs: Term::NonTerminal {
                                name: String::from("Prod3")
                            },
                            rhs: Expression::Choice {
                                exprs: vec![
                                    Expression::Term {
                                        term: Term::NonTerminal {
                                            name: String::from("Test1")
                                        },
                                        rep: Repetition::None
                                    },
                                    Expression::Sequence {
                                        exprs: vec![
                                            Expression::Term {
                                                term: Term::NonTerminal {
                                                    name: String::from("Test2")
                                                },
                                                rep: Repetition::OneOrMore
                                            },
                                            Expression::Difference {
                                                min: Box::new(Expression::Term {
                                                    term: Term::NonTerminal {
                                                        name: String::from("Test3")
                                                    },
                                                    rep: Repetition::None
                                                }),
                                                sub: Box::new(Expression::Term {
                                                    term: Term::NonTerminal {
                                                        name: String::from("Test4")
                                                    },
                                                    rep: Repetition::None
                                                }),
                                                rep: Repetition::None
                                            }
                                        ],
                                        rep: Repetition::None
                                    },
                                ],
                                rep: Repetition::None
                            }
                        },
                        Production {
                            lhs: Term::NonTerminal {
                                name: String::from("Prod4")
                            },
                            rhs: Expression::Difference {
                                min: Box::new(Expression::Term {
                                    term: Term::NonTerminal {
                                        name: String::from("Test1")
                                    },
                                    rep: Repetition::None
                                }),
                                sub: Box::new(Expression::Term {
                                    term: Term::Terminal {
                                        literal: String::from("Test2")
                                    },
                                    rep: Repetition::OneOrMore
                                }),
                                rep: Repetition::None,
                            }
                        }
                    ]
                }
            ))
        );
    }
}
