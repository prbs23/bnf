/// W3C XML Style EBNF Syntax parser
/// Source https://www.w3.org/TR/REC-xml/#sec-notation
///
/// Self described W3C XML style EBNF syntax:
/// Grammar              ::= Production*
/// Production           ::= Name '::=' Choice
/// Name                 ::= NameStartChar NameChar*
/// Choice               ::= SequenceOrDifference ( '|' SequenceOrDifference )*
/// SequenceOrDifference ::= (Item ( '-' Item | Item* ))?
/// Item                 ::= Primary ( '?' | '*' | '+' )?
/// Primary              ::= Name | StringLiteral | CharCode | CharClass | '(' Choice ')'
/// NameStartChar        ::= [A-Z] | "_" | [a-z] | [#xC0-#xD6] | [#xD8-#xF6] | [#xF8-#x2FF] | [#x370-#x37D]
///                        | [#x37F-#x1FFF] | [#x200C-#x200D] | [#x2070-#x218F] | [#x2C00-#x2FEF] | [#x3001-#xD7FF]
///                        | [#xF900-#xFDCF] | [#xFDF0-#xFFFD] | [#x10000-#xEFFFF]
/// NameChar             ::= NameStartChar | "-" | "." | [0-9] | #xB7 | [#x0300-#x036F] | [#x203F-#x2040]
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

// Comment ::= '/*' ( [^*] | '*'+ [^*/] )* '*'* '*/'
pub fn space(i : &str) -> IResult<&str, &str> {
    use nom::branch::alt;
    use nom::bytes::streaming::tag;
    alt((tag("\u{9}"), tag("\u{a}"), tag("\u{d}"), tag("\u{20}")))(i)
}

// Space ::= #x9 | #xA | #xD | #x20
pub fn comment(i : &str) -> IResult<&str, &str> {
    use nom::bytes::streaming::{tag, take_until};
    let (i, _) = tag("/*")(i)?;
    let (i, c) = take_until("*/")(i)?;
    let (i, _) = tag("*/")(i)?;
    return Ok((i, c));
}

// Whitespace  ::= Space | Comment
pub fn whitespace(i : &str) -> IResult<&str, &str> {
    use nom::branch::alt;
    alt((space, comment))(i)
}

// Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]
pub fn character(i : &str) -> IResult<&str, (char, char)> {
    use nom::character::streaming::none_of;
    let (i, c) = none_of("]")(i)?;
    Ok((i, (c,c)))
}

// CharRange ::= Char '-' ( Char - ']' )
pub fn char_range(i : &str) -> IResult<&str, (char, char)> {
    use nom::character::streaming::{char, anychar, none_of};
    let (i, start_char) = anychar(i)?;
    let (i, _) = char('-')(i)?;
    let (i, end_char) = none_of("-")(i)?;
    Ok((i, (start_char, end_char)))
}

// CharCode ::= '#x' [0-9a-fA-F]+
pub fn char_code(i : &str) -> IResult<&str, (char, char)> {
    use nom::bytes::streaming::tag;
    use nom::character::streaming::hex_digit1;
    use nom::{Err, error::ErrorKind};
    use std::convert::TryFrom;
    let (i, _) = tag("#x")(i)?;
    let (i, num) = hex_digit1(i)?;
    match u32::from_str_radix(num, 16) {
        Err(_) => Err(Err::Error((i, ErrorKind::HexDigit))),
        Ok(val) => match char::try_from(val) {
            Err(_) => Err(Err::Error((i, ErrorKind::Char))),
            Ok(c) => Ok((i, (c, c)))
        }
    }
}

// CharCodeRange ::= CharCode '-' CharCode
pub fn char_code_range(i : &str) -> IResult<&str, (char, char)> {
    use nom::character::streaming;
    let (i, start_char) = char_code(i)?;
    let (i, _) = streaming::char('-')(i)?;
    let (i, end_char) = char_code(i)?;
    Ok((i, (start_char.0, end_char.1)))
}

// CharClass ::= '[' '^'? ( Char | CharCode | CharRange | CharCodeRange )+ ']'
pub fn char_class(i : &str) -> IResult<&str, (bool, Vec<(char, char)>)> {
    use nom::{multi::many1, branch::alt, combinator::complete, character::streaming, bytes::streaming::tag};
    use nom::Err;
    let (i, _) = tag("[")(i)?;
    let (i, invert) = match streaming::char('^')(i) {
        Ok((i,_)) => (i, true),
        Err(e) => match e {
            Err::Error(_) => (i, false),
            _ => return Err(e)
        }
    };
    let (i, o) = many1(alt((
        complete(char_code_range),
        complete(char_range),
        complete(char_code),
        complete(character)
    )))(i)?;
    let (i, _) = tag("]")(i)?;
    Ok((i, (invert, o)))
}

// StringLiteral ::= '"' [^"]* '"' | "'" [^']* "'"
pub fn string_literal(i : &str) -> IResult<&str, String> {
    use nom::bytes::streaming::{tag, is_not};
    use nom::branch::alt;
    let (i, delim) = alt((tag("\""), tag("'")))(i)?;
    let (i, o) = is_not(delim)(i)?;
    let (i, _) = tag(delim)(i)?;
    Ok((i, o.to_owned()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::{Err, error::ErrorKind, Needed};

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
        assert_eq!(comment("/* test ** comment **/"), Ok(("", " test ** comment *")));
        assert_eq!(comment("/* test ** comment"), Err(Err::Incomplete(Needed::Size(2))));
    }

    #[test]
    fn whitespace_match() {
        assert_eq!(whitespace("  test"), Ok((" test", " ")));
        assert_eq!(whitespace("/* test ** comment **/"), Ok(("", " test ** comment *")));
    }

    #[test]
    fn char_match() {
        assert_eq!(character("abcd"), Ok(("bcd", ('a', 'a'))));
        assert_eq!(character("\u{2211}abcd"), Ok(("abcd", ('\u{2211}', '\u{2211}'))));
    }

    #[test]
    fn char_range_match() {
        assert_eq!(char_range("a-zd"), Ok(("d", ('a', 'z'))));
        assert_eq!(char_range("\u{0}-\u{2211}"), Ok(("", ('\0', '\u{2211}'))));
        assert_eq!(char_range("a--"), Err(Err::Error(("-", ErrorKind::NoneOf))));
    }

    #[test]
    fn char_code_match() {
        assert_eq!(char_code("#x0000 test"), Ok((" test", ('\0', '\0'))));
        assert_eq!(char_code("#x0B87test"), Ok(("test", ('\u{0b87}', '\u{0b87}'))));
        assert_eq!(char_code("#x0B87#x0b86test"), Ok(("#x0b86test", ('\u{0b87}', '\u{0b87}'))));
        assert_eq!(char_code("#xtest"), Err(Err::Error(("test", ErrorKind::HexDigit))));
    }

    #[test]
    fn char_code_range_match() {
        assert_eq!(char_code_range("#x0000-#xFFFF test"), Ok((" test", ('\0', '\u{ffff}'))));
        assert_eq!(char_code_range("#x04D2-#x0b87test"), Ok(("test", ('\u{04D2}', '\u{0b87}'))));
        assert_eq!(char_code_range("#x04D2-#x0b87#x0000test"), Ok(("#x0000test", ('\u{04D2}', '\u{0b87}'))));
        assert_eq!(char_code_range("#xdead=#xbeef"), Err(Err::Error(("=#xbeef", ErrorKind::Char))));
        assert_eq!(char_code_range("#x04d2-#xtest"), Err(Err::Error(("test", ErrorKind::HexDigit))));
    }

    #[test]
    fn char_class_match() {
        assert_eq!(char_class("[^abcd]"), Ok(("", (true, vec![('a', 'a'), ('b','b'), ('c', 'c'), ('d', 'd')]))));
        assert_eq!(char_class("[a-zA-Z]"), Ok(("", (false, vec![('a', 'z'), ('A', 'Z')]))));
        assert_eq!(char_class("[\u{0391}-Ϋ]"), Ok(("", (false, vec![('Α', 'Ϋ')]))));
        assert_eq!(char_class("[^#x0061-#x007a#x41-#x5A]"), Ok(("", (true, vec![('a', 'z'), ('A', 'Z')]))));
        assert_eq!(char_class("[a-z#x41-#x5A]"), Ok(("", (false, vec![('a', 'z'), ('A', 'Z')]))));
        assert_eq!(char_class("[^a-z#x41-#x5A#x0xyz]"), Ok(("", (true, vec![('a', 'z'), ('A', 'Z'), ('\0', '\0'), ('x', 'x'), ('y', 'y'), ('z', 'z')]))));
    }

    #[test]
    fn string_literal_match() {
        assert_eq!(string_literal("'Hello WorldΘ'"), Ok(("", String::from("Hello WorldΘ"))));
        assert_eq!(string_literal("\"Hello World\""), Ok(("", String::from("Hello World"))));
        assert_eq!(string_literal("\"'Hello World\"'"), Ok(("'", String::from("'Hello World"))));
        assert_eq!(string_literal(" \"Hello World\""), Err(Err::Error((" \"Hello World\"", ErrorKind::Tag))));
        assert_eq!(string_literal("'Hello Worl"), Err(Err::Incomplete(Needed::Size(1))));
    }
}