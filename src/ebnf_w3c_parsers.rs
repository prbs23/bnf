/// W3C XML Style EBNF Syntax parser
/// Source https://www.w3.org/TR/REC-xml/#sec-notation
///
/// Self described W3C XML style EBNF syntax:
/// Grammar              ::= Production*
/// Production           ::= Name '::=' Choice
/// Name                 ::= NameStartChar NameChar*
/// Choice               ::= SequenceOrDifference ( '|' SequenceOrDifference )*
/// SequenceOrDifference ::= (Item ( '-' Item | Item* ))
/// Item                 ::= Primary ( '?' | '*' | '+' )?
/// Primary              ::= Name | StringLiteral | CharCode | CharClass | '(' Choice ')'
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
    Optional,
    OptionalMulti,
    OneOrMore,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TermType {
    Terminal(String),
    TerminalClass(bool, Vec<(char, char)>),
    NonTerminal(String),
    Difference(Box<Term>, Box<Term>),
    Sequence(Vec<Term>),
    Choice(Vec<Term>)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
    term_type : TermType,
    repetition : Repetition
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Production {
    name: String,
    term: Term
}

pub fn range(start_char : char, end_char : char) -> impl Fn(&str) -> IResult<&str, char>  {
    use nom::{Needed, Err, error::ErrorKind};
    move |i: &str| match (i).chars().next().map(|c| (c, (c >= start_char) && (c <= end_char))) {
        None => Err(Err::Incomplete(Needed::Size(1))),
        Some((_, false)) => Err(Err::Error((i, ErrorKind::Char))),
        Some((c, true)) => Ok((&i[c.len_utf8()..], c)),
    }
}

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
pub fn char_class(i : &str) -> IResult<&str, Term> {
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
    Ok((i, Term {term_type: TermType::TerminalClass(invert, o), repetition: Repetition::None}))
}

// StringLiteral ::= '"' [^"]* '"' | "'" [^']* "'"
pub fn string_literal(i : &str) -> IResult<&str, Term> {
    use nom::bytes::streaming::{tag, is_not};
    use nom::branch::alt;
    let (i, delim) = alt((tag("\""), tag("'")))(i)?;
    let (i, o) = is_not(delim)(i)?;
    let (i, _) = tag(delim)(i)?;
    Ok((i, Term {term_type: TermType::Terminal(o.to_owned()), repetition: Repetition::None}))
}

// NameStartChar ::= [A-Z] | "_" | [a-z] | [#xC0-#xD6] | [#xD8-#xF6] | [#xF8-#x2FF] | [#x370-#x37D]
//                 | [#x37F-#x1FFF] | [#x200C-#x200D] | [#x2070-#x218F] | [#x2C00-#x2FEF] | [#x3001-#xD7FF]
//                 | [#xF900-#xFDCF] | [#xFDF0-#xFFFD] | [#x10000-#xEFFFF]
pub fn name_start_char(i : &str) -> IResult<&str, char> {
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
        range('\u{10000}', '\u{effff}')
    ))(i)
}

// NameChar ::= NameStartChar | "." | [0-9] | #xB7 | [#x0300-#x036F] | [#x203F-#x2040]
pub fn name_char(i : &str) -> IResult<&str, char> {
    use nom::branch::alt;
    use nom::character::streaming::char;
    alt((
        name_start_char,
        char('.'),
        range('0','9'),
        char('\u{b7}'),
        range('\u{300}', '\u{36f}'),
        range('\u{203f}', '\u{2040}')
    ))(i)
}

// Name ::= NameStartChar NameChar*
pub fn name(i : &str) -> IResult<&str, String> {
    use nom::multi::fold_many0;
    let (i, s) = name_start_char(i)?;
    let (i, o) = fold_many0(name_char, s.to_string(), |mut acc : String, item| {acc.push(item); acc})(i)?;
    Ok((i, o))
}

// Primary ::= Name | StringLiteral | CharCode | CharClass | '(' Choice ')'
pub fn primary(i : &str) -> IResult<&str, Term> {
    use nom::combinator::{map, not, complete};
    use nom::branch::alt;
    use nom::sequence::{tuple, terminated};
    use nom::character::streaming::char;
    use nom::multi::many0;
    use nom::bytes::streaming::tag;
    alt((
        map(terminated(name, not(complete(tuple((many0(whitespace), tag("::=")))))), |s : String | Term {term_type: TermType::NonTerminal(s), repetition: Repetition::None}),
        string_literal,
        map(char_code, |c : (char, char)| Term {term_type: TermType::Terminal(c.0.to_string()), repetition: Repetition::None}),
        char_class,
        map(tuple((char('('), choice, char(')'))), |tup : (char, Term, char)| tup.1)
    ))(i)
}

// Item ::= Primary ( '?' | '*' | '+' )?
pub fn item(i : &str) -> IResult<&str, Term> {
    use nom::combinator::{opt, map};
    use nom::sequence::tuple;
    use nom::branch::alt;
    use nom::character::streaming::char;
    map( tuple((primary, opt(alt((char('?'), char('*'), char('+')))))), | t : (Term, Option<char>) | Term{term_type: t.0.term_type, repetition: match t.1 {
        Some(c) => match c {
            '?' => Repetition::Optional,
            '*' => Repetition::OptionalMulti,
            '+' => Repetition::OneOrMore,
            _ => Repetition::None
        },
        None => Repetition::None
    }})(i)
}

// SequenceOrDifference ::= (Item ( '-' Item | Item* ))
pub fn sequence_or_difference(i : &str) -> IResult<&str, Term> {
    use nom::combinator::{map, complete};
    use nom::sequence::tuple;
    use nom::branch::alt;
    use nom::multi::{many0, many1, separated_nonempty_list};
    use nom::character::streaming::char;
    alt((
        map(tuple((item, many0(whitespace), char('-'), many0(whitespace), item)),
            | t : (Term, Vec<&str>, char, Vec<&str>, Term) | Term {term_type: TermType::Difference(Box::new(t.0), Box::new(t.4)), repetition: Repetition::None}),
        map(separated_nonempty_list(complete(many1(whitespace)), item), | vec : Vec<Term> | Term {term_type: TermType::Sequence(vec), repetition: Repetition::None})
        ))(i)
}

// Choice ::= SequenceOrDifference ( '|' SequenceOrDifference )*
pub fn choice(i : &str) -> IResult<&str, Term> {
    use nom::combinator::{map, complete};
    use nom::sequence::tuple;
    use nom::multi::{many0, separated_nonempty_list};
    use nom::character::streaming::char;
    map(separated_nonempty_list(complete(tuple((many0(whitespace), char('|'), many0(whitespace)))), sequence_or_difference),
        | vec : Vec<Term> | Term {term_type: TermType::Choice(vec), repetition: Repetition::None})(i)
}

// Production ::= Name '::=' Choice
pub fn production(i: &str) -> IResult<&str, Production> {
    use nom::bytes::streaming::tag;
    use nom::multi::many0;
    let (i, name) = name(i)?;
    let (i, _) = many0(whitespace)(i)?;
    let (i, _) = tag("::=")(i)?;
    let (i, _) = many0(whitespace)(i)?;
    let (i, term) = choice(i)?;
    Ok((i, Production {name, term}))
}

// Grammar ::= Production*
pub fn grammar(i : &str) -> IResult<&str, Vec<Production>> {
    use nom::combinator::complete;
    use nom::multi::{many0, separated_nonempty_list};
    separated_nonempty_list(complete(many0(whitespace)), production)(i)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::{Err, error::ErrorKind, Needed};

    #[test]
    fn range_test() {
        assert_eq!(range('a', 'z')("b"), Ok(("", 'b')));
        assert_eq!(range('a', 'z')("A"), Err(Err::Error(("A", ErrorKind::Char))));
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
        assert_eq!(char_class("[^abcd]"), Ok(("", Term {term_type : TermType::TerminalClass(true, vec![('a', 'a'), ('b','b'), ('c', 'c'), ('d', 'd')]), repetition: Repetition::None})));
        assert_eq!(char_class("[a-zA-Z]"), Ok(("", Term {term_type : TermType::TerminalClass(false, vec![('a', 'z'), ('A', 'Z')]), repetition: Repetition::None})));
        assert_eq!(char_class("[\u{0391}-Ϋ]"), Ok(("", Term {term_type : TermType::TerminalClass(false, vec![('Α', 'Ϋ')]), repetition: Repetition::None})));
        assert_eq!(char_class("[^#x0061-#x007a#x41-#x5A]"), Ok(("", Term {term_type : TermType::TerminalClass(true, vec![('a', 'z'), ('A', 'Z')]), repetition: Repetition::None})));
        assert_eq!(char_class("[a-z#x41-#x5A]"), Ok(("", Term {term_type : TermType::TerminalClass(false, vec![('a', 'z'), ('A', 'Z')]), repetition: Repetition::None})));
        assert_eq!(char_class("[^a-z#x41-#x5A#x0xyz]"), Ok(("", Term {term_type : TermType::TerminalClass(true, vec![('a', 'z'), ('A', 'Z'), ('\0', '\0'), ('x', 'x'), ('y', 'y'), ('z', 'z')]), repetition: Repetition::None})));
    }

    #[test]
    fn string_literal_match() {
        assert_eq!(string_literal("'Hello WorldΘ'"), Ok(("", Term {term_type : TermType::Terminal(String::from("Hello WorldΘ")), repetition: Repetition::None})));
        assert_eq!(string_literal("\"Hello World\""), Ok(("", Term {term_type : TermType::Terminal(String::from("Hello World")), repetition: Repetition::None})));
        assert_eq!(string_literal("\"'Hello World\"'"), Ok(("'", Term {term_type : TermType::Terminal(String::from("'Hello World")), repetition: Repetition::None})));
        assert_eq!(string_literal(" \"Hello World\""), Err(Err::Error((" \"Hello World\"", ErrorKind::Tag))));
        assert_eq!(string_literal("'Hello Worl"), Err(Err::Incomplete(Needed::Size(1))));
    }

    #[test]
    fn name_start_char_match() {
        assert_eq!(name_start_char("Abcd"), Ok(("bcd", 'A')));
        assert_eq!(name_start_char("\u{f8}"), Ok(("", '\u{f8}')));
        assert_eq!(name_start_char("0Abcd"), Err(Err::Error(("0Abcd", ErrorKind::Char))));
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
    fn primary_match() {
        assert_eq!(primary("TestName \"Test\" #xc0 [#xC0-#xD6]"), Ok((" \"Test\" #xc0 [#xC0-#xD6]", Term {term_type : TermType::NonTerminal(String::from("TestName")), repetition: Repetition::None})));
        assert_eq!(primary("\"Test\" #xc0 [#xC0-#xD6] TestName"), Ok((" #xc0 [#xC0-#xD6] TestName", Term {term_type : TermType::Terminal(String::from("Test")), repetition: Repetition::None})));
        assert_eq!(primary("#xc0 [#xC0-#xD6] TestName \"Test\""), Ok((" [#xC0-#xD6] TestName \"Test\"", Term {term_type : TermType::Terminal(String::from("\u{c0}")), repetition: Repetition::None})));
        assert_eq!(primary("[#xC0-#xD6] TestName \"Test\" #xc0"), Ok((" TestName \"Test\" #xc0", Term {term_type : TermType::TerminalClass(false, vec![('\u{c0}','\u{d6}')]), repetition: Repetition::None})));
        assert_eq!(primary("(Test1+ | Test2 - Test3 | 'Test4') Test5 "), Ok((" Test5 ", Term {
            term_type: TermType::Choice(vec![
                Term {term_type: TermType::Sequence(vec![Term {term_type: TermType::NonTerminal(String::from("Test1")), repetition: Repetition::OneOrMore}]), repetition: Repetition::None},
                Term {term_type: TermType::Difference(
                    Box::new(Term {term_type: TermType::NonTerminal(String::from("Test2")), repetition: Repetition::None}),
                    Box::new(Term {term_type: TermType::NonTerminal(String::from("Test3")), repetition: Repetition::None})), repetition: Repetition::None},
                Term {term_type: TermType::Sequence(vec![
                    Term {term_type: TermType::Terminal(String::from("Test4")), repetition: Repetition::None}]), repetition: Repetition::None}
            ]),
            repetition: Repetition::None
        })));
    }

    #[test]
    fn item_match() {
        assert_eq!(item("TestItem "), Ok((" ", Term {term_type: TermType::NonTerminal(String::from("TestItem")), repetition: Repetition::None})));
        assert_eq!(item("TestItem*"), Ok(("", Term {term_type: TermType::NonTerminal(String::from("TestItem")), repetition: Repetition::OptionalMulti})));
        assert_eq!(item("TestItem?"), Ok(("", Term {term_type: TermType::NonTerminal(String::from("TestItem")), repetition: Repetition::Optional})));
        assert_eq!(item("TestItem+"), Ok(("", Term {term_type: TermType::NonTerminal(String::from("TestItem")), repetition: Repetition::OneOrMore})));
    }

    #[test]
    fn sequence_or_difference_match() {
        assert_eq!(sequence_or_difference("Test+ -  'Item' Next"), Ok((" Next", Term {
            term_type: TermType::Difference(
                Box::new(Term{term_type: TermType::NonTerminal(String::from("Test")), repetition: Repetition::OneOrMore}),
                Box::new(Term{term_type: TermType::Terminal(String::from("Item")), repetition: Repetition::None})),
            repetition: Repetition::None
        })));
        assert_eq!(sequence_or_difference("Test+  'Item' Next?"), Ok(("", Term {
            term_type: TermType::Sequence(vec![
                Term {term_type: TermType::NonTerminal(String::from("Test")), repetition: Repetition::OneOrMore},
                Term {term_type: TermType::Terminal(String::from("Item")), repetition: Repetition::None},
                Term {term_type: TermType::NonTerminal(String::from("Next")), repetition: Repetition::Optional}
            ]),
            repetition: Repetition::None
        })));
    }

    #[test]
    fn choice_match() {
        assert_eq!(choice("Test1+ | Test2 - Test3 | 'Test4' Test5 "), Ok((" ", Term {
            term_type: TermType::Choice(vec![
                Term {term_type: TermType::Sequence(vec![Term {term_type: TermType::NonTerminal(String::from("Test1")), repetition: Repetition::OneOrMore}]), repetition: Repetition::None},
                Term {term_type: TermType::Difference(
                    Box::new(Term {term_type: TermType::NonTerminal(String::from("Test2")), repetition: Repetition::None}),
                    Box::new(Term {term_type: TermType::NonTerminal(String::from("Test3")), repetition: Repetition::None})), repetition: Repetition::None},
                Term {term_type: TermType::Sequence(vec![
                    Term {term_type: TermType::Terminal(String::from("Test4")), repetition: Repetition::None},
                    Term {term_type: TermType::NonTerminal(String::from("Test5")), repetition: Repetition::None}]), repetition: Repetition::None}
            ]),
            repetition: Repetition::None
        })));
    }

    #[test]
    fn production_match() {
        assert_eq!(production("Test1 ::= 'Test2'? | Test3 - Test4+ | Test5 Test6* "), Ok((" ", Production {
            name: String::from("Test1"),
            term: Term {
                term_type: TermType::Choice(vec![
                    Term {term_type: TermType::Sequence(vec![Term {term_type: TermType::Terminal(String::from("Test2")), repetition: Repetition::Optional}]), repetition: Repetition::None},
                    Term {term_type: TermType::Difference(
                        Box::new(Term {term_type: TermType::NonTerminal(String::from("Test3")), repetition: Repetition::None}),
                        Box::new(Term {term_type: TermType::NonTerminal(String::from("Test4")), repetition: Repetition::OneOrMore})
                    ), repetition: Repetition::None},
                    Term {term_type: TermType::Sequence(vec![
                        Term {term_type: TermType::NonTerminal(String::from("Test5")), repetition: Repetition::None},
                        Term {term_type: TermType::NonTerminal(String::from("Test6")), repetition: Repetition::OptionalMulti}
                    ]), repetition: Repetition::None}
                ]),
                repetition: Repetition::None
            }
        }))
        )
    }

    #[test]
    fn grammar_match() {
        assert_eq!(grammar("\
Test1 ::= 'Test2'? | Test3 - Test4+ | Test5 Test6*
Test2 ::= 'test2'
Test5 ::= Test3 - Test4 "
        ), Ok((" ", vec![
            Production {
                name: String::from("Test1"),
                term: Term {
                    term_type: TermType::Choice(vec![
                        Term {term_type: TermType::Sequence(vec![Term {term_type: TermType::Terminal(String::from("Test2")), repetition: Repetition::Optional}]), repetition: Repetition::None},
                        Term {term_type: TermType::Difference(
                            Box::new(Term {term_type: TermType::NonTerminal(String::from("Test3")), repetition: Repetition::None}),
                            Box::new(Term {term_type: TermType::NonTerminal(String::from("Test4")), repetition: Repetition::OneOrMore})
                        ), repetition: Repetition::None},
                        Term {term_type: TermType::Sequence(vec![
                            Term {term_type: TermType::NonTerminal(String::from("Test5")), repetition: Repetition::None},
                            Term {term_type: TermType::NonTerminal(String::from("Test6")), repetition: Repetition::OptionalMulti}
                        ]), repetition: Repetition::None}
                    ]),
                    repetition: Repetition::None
                }
            },
            Production {
                name: String::from("Test2"),
                term: Term {
                    term_type: TermType::Choice(vec![
                        Term { term_type: TermType::Sequence(vec![Term {term_type: TermType::Terminal(String::from("test2")), repetition: Repetition::None}]), repetition: Repetition::None}
                    ]),
                    repetition: Repetition::None
                }
            },
            Production {
                name: String::from("Test5"),
                term: Term {
                    term_type: TermType::Choice(vec![
                        Term {
                            term_type: TermType::Difference(
                                Box::new(Term {term_type: TermType::NonTerminal(String::from("Test3")), repetition: Repetition::None}),
                                Box::new(Term {term_type: TermType::NonTerminal(String::from("Test4")), repetition: Repetition::None})
                            ),
                            repetition: Repetition::None
                        }
                    ]),
                    repetition: Repetition::None
                }
            }
        ])));
    }
}
