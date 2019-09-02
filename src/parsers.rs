use expression::Expression;
use grammar::Grammar;
use production::Production;
use term::Term;

named!(pub prod_lhs< &str, Term >,
    do_parse!(
            nt: delimited!(char!('<'), take_until!(">"), ws!(char!('>'))) >>
            _ret: ws!(tag!("::=")) >>
            (Term::Nonterminal(String::from(nt)))
    )
);

named!(pub terminal< &str, Term >,
    do_parse!(
        t: alt!(
            delimited!(char!('"'), take_until!("\""), ws!(char!('"'))) |
            delimited!(char!('\''), take_until!("'"), ws!(char!('\'')))
            ) >>
        (Term::Terminal(String::from(t)))
    )
);

named!(pub nonterminal< &str, Term >,
    do_parse!(
        nt: complete!(delimited!(char!('<'), take_until!(">"), ws!(char!('>')))) >>
        ws!(not!(complete!(tag!("::=")))) >>
        (Term::Nonterminal(String::from(nt)))
    )
);

named!(pub term< &str, Term >, alt!(terminal | nonterminal));

named!(pub term_complete< &str, Term >,
    do_parse!(
        t: term >>
        eof!() >>
        (t)
    )
);

named!(pub expression_next< &str, &str >,
    do_parse!(
        ws!(char!('|')) >>
        ret: recognize!(peek!(complete!(expression))) >>
        (ret)
    )
);

named!(pub expression< &str, Expression >,
    do_parse!(
        peek!(term) >>
        terms: many1!(complete!(term)) >>
        ws!(
            alt!(
                recognize!(peek!(complete!(eof!()))) |
                recognize!(peek!(complete!(char!(';')))) |
                expression_next |
                recognize!(peek!(complete!(prod_lhs)))
            )
        ) >>
        (Expression::from_parts(terms))
    )
);

named!(pub expression_complete< &str, Expression >,
    do_parse!(
        e: expression >>
        eof!() >>
        (e)
    )
);

named!(pub production< &str, Production >,
    do_parse!(
        lhs: ws!(prod_lhs) >>
        rhs: many1!(complete!(expression)) >>
        ws!(
            alt!(
                recognize!(peek!(complete!(eof!()))) |
                tag!(";") |
                recognize!(peek!(complete!(prod_lhs)))
            )
        ) >>
        (Production::from_parts(lhs, rhs))
    )
);

named!(pub production_complete< &str, Production >,
    do_parse!(
        p: production >>
        eof!() >>
        (p)
    )
);

named!(pub grammar< &str, Grammar >,
    do_parse!(
        peek!(production) >>
        prods: many1!(complete!(production)) >>
        (Grammar::from_parts(prods))
    )
);

named!(pub grammar_complete< &str, Grammar >,
    do_parse!(
        g: grammar >>
        eof!() >>
        (g)
    )
);

#[cfg(test)]
mod tests {
    use super::*;

    fn construct_terminal_tuple() -> (Term, String) {
        let terminal_pattern = "\"terminal pattern\"";
        let terminal_value = "terminal pattern";
        let terminal_object = Term::Terminal(String::from(terminal_value));

        (terminal_object, String::from(terminal_pattern))
    }

    #[test]
    fn terminal_match() {
        let terminal_tuple = construct_terminal_tuple();
        assert_eq!(
            terminal_tuple.0,
            terminal(terminal_tuple.1.as_str()).unwrap().1
        );
    }

    fn construct_nonterminal_tuple() -> (Term, String) {
        let nonterminal_pattern = "<nonterminal-pattern>";
        let nonterminal_value = "nonterminal-pattern";
        let nonterminal_object = Term::Nonterminal(String::from(nonterminal_value));

        (nonterminal_object, String::from(nonterminal_pattern))
    }

    #[test]
    fn nonterminal_match() {
        let nonterminal_tuple = construct_nonterminal_tuple();
        assert_eq!(
            nonterminal_tuple.0,
            nonterminal(nonterminal_tuple.1.as_str()).unwrap().1
        );
    }

    fn construct_expression_tuple() -> (Expression, String) {
        let nonterminal_tuple = construct_nonterminal_tuple();
        let terminal_tuple = construct_terminal_tuple();
        let expression_pattern = nonterminal_tuple.1 + &terminal_tuple.1;
        let expression_object = Expression::from_parts(vec![nonterminal_tuple.0, terminal_tuple.0]);

        (expression_object, expression_pattern)
    }

    #[test]
    fn expression_match() {
        let expression_tuple = construct_expression_tuple();
        assert_eq!(
            expression_tuple.0,
            expression(expression_tuple.1.as_str()).unwrap().1
        );
    }

    fn construct_production_tuple() -> (Production, String) {
        let expression_tuple = construct_expression_tuple();
        let nonterminal_tuple = construct_nonterminal_tuple();
        let terminal_tuple = construct_nonterminal_tuple();
        let production_pattern =
            nonterminal_tuple.1 + "::=" + &expression_tuple.1 + "|" + &terminal_tuple.1 + ";";
        let production_object = Production::from_parts(
            nonterminal_tuple.0,
            vec![
                expression_tuple.0.clone(),
                Expression::from_parts(vec![terminal_tuple.0]),
            ],
        );

        (production_object, production_pattern)
    }

    #[test]
    fn production_match() {
        let production_tuple = construct_production_tuple();
        let parsed = production(production_tuple.1.as_str());
        assert_eq!(production_tuple.0, parsed.unwrap().1);
    }

    fn construct_grammar_tuple() -> (Grammar, String) {
        let production_tuple = construct_production_tuple();
        let grammar_pattern = production_tuple.1.clone() + &production_tuple.1;
        let grammar_object = Grammar::from_parts(vec![
            construct_production_tuple().0.clone(),
            construct_production_tuple().0,
        ]);

        (grammar_object, String::from(grammar_pattern))
    }

    #[test]
    fn grammar_match() {
        let grammar_tuple = construct_grammar_tuple();
        assert_eq!(
            grammar_tuple.0,
            grammar(grammar_tuple.1.as_str()).unwrap().1
        );
    }
}
