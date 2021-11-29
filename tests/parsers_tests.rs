use nom::{
    error::{ErrorKind, VerboseError, VerboseErrorKind},
    Err as NomErr,
};
use worst_parser::{
    parsers::{
        parse_atomic_formula, parse_atomic_formula_skeleton, parse_base_type, parse_constants_def,
        parse_constraint_def, parse_gd, parse_literal, parse_name, parse_ordering_def,
        parse_ordering_defs, parse_p_class, parse_predicates_def, parse_term, parse_types,
        parse_types_def, parse_variable, Res,
    },
    syntaxtree::{
        AtomicFormula, ConstraintDef, GoalDefinition, Literal, OrderingDef, Predicate, PredicateId,
        SubtaskId, Term, TypedList, Types,
    },
};
use worst_parser::{
    parsers::{parse_type, parse_typed_lists, whitespace},
    syntaxtree::{Type, TypedLists, VariableId},
};

type DefRes<'a> = Res<&'a str, &'a str>;

#[test]
fn test_whitespace() {
    assert_eq!(whitespace(" \t\n"), DefRes::Ok(("", " \t\n")));

    assert_eq!(whitespace(""), DefRes::Ok(("", "")));

    assert_eq!(whitespace(" a "), DefRes::Ok(("a ", " ")));

    assert_eq!(whitespace("a "), DefRes::Ok(("a ", "")));
}

/**
 * <types-def> ::= (:types <types>+)
 */
#[test]
fn test_types_def() {
    let types_1 = "types a b c - foo d e f - bar foo bar - object";
    let types_2 = "object";
    let rest = " asdf qwer tyui ghjk";

    let types_def = {
        let mut types_def = "(:types ".to_owned();
        types_def.push_str(types_1);
        types_def.push(' ');
        types_def.push_str(types_2);
        types_def.push(')');
        types_def.push_str(rest);
        types_def
    };

    let (_, types_1_ast) = parse_types(types_1).unwrap();
    let (_, types_2_ast) = parse_types(types_2).unwrap();

    assert_eq!(
        parse_types_def(types_def.as_str()),
        Res::Ok((rest, vec![types_1_ast, types_2_ast]))
    );
}

/**
 * <types> ::= <typed list (name)>
 *     | <base-type>
 */
#[test]
fn test_types() {
    let typed_list = "a b c - foo d e - bar";
    let base_type = "asdf ghjk qwer tyui";

    let (_, typed_list_ast) = parse_typed_lists(parse_name)(typed_list).unwrap();
    let (_, base_type_ast) = parse_base_type(base_type).unwrap();

    assert_eq!(
        parse_types(typed_list),
        Res::Ok(("", Types::Subtype(typed_list_ast)))
    );

    assert_eq!(
        parse_types(base_type),
        Res::Ok((" ghjk qwer tyui", Types::BaseType(base_type_ast)))
    );
}

/**
 * <constants-def> ::=
 *     (:constants <typed list (name)>)
 */
#[test]
fn test_parse_constants_def() {
    let constant_list = "x y z - foo a b - bar u v w - baz";
    let (_, typed_list_ast) = parse_typed_lists(parse_name)(constant_list).unwrap();

    let constants_def = {
        let mut constants_def = "(:constants ".to_owned();
        constants_def.push_str(constant_list);
        constants_def.push(')');
        constants_def
    };

    assert_eq!(
        parse_constants_def(constants_def.as_str()),
        Res::Ok(("", typed_list_ast))
    );
}

/**
 * <predicates-def> ::=
 *     (:predicates <atomic-formula-skeleton>+)
 */
#[test]
fn test_predicates_def() {
    let predicate_1 = "(predicate_1 x y z - object a b c - tree)";
    let predicate_2 = "(predicate_2 foo bar - some_type baz - other_type)";
    let predicates = {
        let mut predicates = "(:predicates ".to_owned();
        predicates.push_str(predicate_1);
        predicates.push('\n');
        predicates.push_str(predicate_2);
        predicates.push(')');
        predicates
    };

    let (_, predicate_1_ast) = parse_atomic_formula_skeleton(predicate_1).unwrap();
    let (_, predicate_2_ast) = parse_atomic_formula_skeleton(predicate_2).unwrap();

    assert_eq!(
        parse_predicates_def(predicates.as_str()),
        Res::Ok(("", vec![predicate_1_ast, predicate_2_ast]))
    );
}

/**
 * <atomic-formula-skeleton> ::=
 *     (<predicate> <typed list (variable)>)
 */
#[test]
fn test_atomic_formula_skeleton() {
    assert_eq!(
        parse_atomic_formula_skeleton("(predicate_1 foo bar baz - object x y z - box)"),
        Res::Ok((
            "",
            Predicate {
                predicate: PredicateId {
                    name: "predicate_1"
                },
                parameters: TypedLists {
                    elems: vec![
                        TypedList {
                            elem_type: Type::Single("object"),
                            elems: vec![
                                VariableId { name: "foo" },
                                VariableId { name: "bar" },
                                VariableId { name: "baz" }
                            ]
                        },
                        TypedList {
                            elem_type: Type::Single("box"),
                            elems: vec![
                                VariableId { name: "x" },
                                VariableId { name: "y" },
                                VariableId { name: "z" }
                            ]
                        }
                    ]
                }
            }
        ))
    );

    assert_eq!(
        parse_atomic_formula_skeleton("(predicate_1 foo bar baz - (either object box tree)) test"),
        Res::Ok((
            " test",
            Predicate {
                predicate: PredicateId {
                    name: "predicate_1"
                },
                parameters: TypedLists {
                    elems: vec![TypedList {
                        elem_type: Type::List(vec!["object", "box", "tree"]),
                        elems: vec![
                            VariableId { name: "foo" },
                            VariableId { name: "bar" },
                            VariableId { name: "baz" }
                        ]
                    },]
                }
            }
        ))
    );
}

#[test]
fn test_typed_list() {
    assert_eq!(
        parse_typed_lists(parse_name)("a b c - object"),
        Res::Ok((
            "",
            TypedLists {
                elems: vec![TypedList {
                    elems: vec!["a", "b", "c"],
                    elem_type: Type::Single("object"),
                }]
            }
        ))
    );

    assert_eq!(
        parse_typed_lists(parse_variable)("a b c - object"),
        Res::Ok((
            "",
            TypedLists {
                elems: vec![TypedList {
                    elems: vec![
                        VariableId { name: "a" },
                        VariableId { name: "b" },
                        VariableId { name: "c" }
                    ],
                    elem_type: Type::Single("object")
                }]
            }
        ))
    );

    assert_eq!(
        parse_typed_lists(parse_variable)("a b c - object d e f - box"),
        Res::Ok((
            "",
            TypedLists {
                elems: vec![
                    TypedList {
                        elems: vec![
                            VariableId { name: "a" },
                            VariableId { name: "b" },
                            VariableId { name: "c" }
                        ],
                        elem_type: Type::Single("object")
                    },
                    TypedList {
                        elems: vec![
                            VariableId { name: "d" },
                            VariableId { name: "e" },
                            VariableId { name: "f" }
                        ],
                        elem_type: Type::Single("box")
                    }
                ]
            }
        ))
    );

    assert_eq!(
        parse_typed_lists(parse_variable)("a b c - object d e f"),
        Res::Ok((
            "d e f",
            TypedLists {
                elems: vec![TypedList {
                    elems: vec![
                        VariableId { name: "a" },
                        VariableId { name: "b" },
                        VariableId { name: "c" }
                    ],
                    elem_type: Type::Single("object"),
                }],
            }
        ))
    );
}

#[test]
fn test_type() {
    assert_eq!(
        parse_type("test_type"),
        Res::Ok(("", Type::Single("test_type")))
    );

    assert_eq!(
        parse_type("(either type-1 type-2 type-3)"),
        Res::Ok(("", Type::List(vec!["type-1", "type-2", "type-3"])))
    );
}

/**
 * <ordering-defs> ::= () | <ordering-def>
 *     | (and <ordering-def>+)
 */
#[test]
fn test_ordering_defs() {
    let def_1 = "(t1 < t2)";
    let def_2 = "(t2 < t3)";
    let def_3 = "(t3 < t1)";

    let rest = "asdlfkj ()(*???";

    let (_, def_1_ast) = parse_ordering_def(def_1).unwrap();
    let (_, def_2_ast) = parse_ordering_def(def_2).unwrap();
    let (_, def_3_ast) = parse_ordering_def(def_3).unwrap();

    let defs = {
        let mut defs = "(\tand\n".to_owned();
        defs.push_str(def_1);
        defs.push('\r');
        defs.push_str(def_2);
        defs.push(' ');
        defs.push_str(def_3);
        defs.push_str(" )");
        defs.push_str(rest);
        defs
    };

    assert_eq!(
        parse_ordering_defs(defs.as_str()),
        Res::Ok((rest, vec![def_1_ast, def_2_ast, def_3_ast]))
    );

    let (_, def_1_ast) = parse_ordering_def(def_1).unwrap();
    assert_eq!(parse_ordering_defs(def_1), Res::Ok(("", vec![def_1_ast])));

    assert_eq!(parse_ordering_defs("() asdf"), Res::Ok((" asdf", vec![])));
}

/**
 * <ordering-def> ::=
 *     (<subtask-id> "<" <subtask-id>)
 */
#[test]
fn test_ordering_def() {
    assert_eq!(
        parse_ordering_def("(t1 < t2)"),
        Res::Ok((
            "",
            OrderingDef {
                first: SubtaskId { name: "t1" },
                second: SubtaskId { name: "t2" }
            }
        ))
    );

    assert_eq!(
        parse_ordering_def("(\nt1\t< t2\r   )"),
        Res::Ok((
            "",
            OrderingDef {
                first: SubtaskId { name: "t1" },
                second: SubtaskId { name: "t2" }
            }
        ))
    );
}

/**
 * <constraint-def> ::= ()
 *     | (not (= <term> <term>))
 *     | (= <term> <term>)
 */
#[test]
fn test_constraint_def() {
    let empty = "( )rest";
    let neq = "( not ( = t1 t2 ) )rest";
    let eq = "( = t1 t2 )rest";

    assert_eq!(parse_constraint_def(empty), Res::Ok(("rest", None)));

    assert_eq!(
        parse_constraint_def(neq),
        Res::Ok((
            "rest",
            Some(ConstraintDef::NEq(Term::Name("t1"), Term::Name("t2")))
        ))
    );

    assert_eq!(
        parse_constraint_def(eq),
        Res::Ok((
            "rest",
            Some(ConstraintDef::Eq(Term::Name("t1"), Term::Name("t2")))
        ))
    );
}
/**
 * <gd> ::= ()
 * <gd> ::= <atomic formula (term)>
 * <gd> ::=:negative-preconditions <literal (term)>
 * <gd> ::= (and <gd>*)
 * <gd> ::=:disjunctive-preconditions (or <gd>*)
 * <gd> ::=:disjunctive-preconditions (not <gd>)
 * <gd> ::=:disjunctive-preconditions (imply <gd> <gd>)
 * <gd> ::=:existential-preconditions
 *     (exists (<typed list (variable)>*) <gd>)
 * <gd> ::=:universal-preconditions
 *     (forall (<typed list (variable)>*) <gd>)
 * <gd> ::= (= <term> <term>)
 */
#[test]
fn test_gd() {
    let formula = "( pred_01 term_01 term_02 )";
    let literal = "( not ( pred_02 term_03 term_04 ) )";
    let gd_1 = literal.clone();
    let gd_2 = formula.clone();
    let typed_lists = "a b c - object d e - box f - thingamajig";
    let rest = " rest";

    // <gd> ::= ()
    {
        assert_eq!(parse_gd("( )rest"), Ok(("rest", GoalDefinition::Empty)));
    }
    // <gd> ::= <atomic formula (term)>
    {
        let (_, formula_ast) = parse_atomic_formula(parse_term)(formula).unwrap();
        let gd_formula = {
            let mut gd_formula = formula.to_owned();
            gd_formula.push_str(rest);
            gd_formula
        };
        assert_eq!(
            parse_gd(&gd_formula),
            Ok((rest, GoalDefinition::Formula(formula_ast)))
        );
    }
    // <gd> ::=:negative-preconditions <literal (term)>
    {
        let (_, literal_ast) = parse_literal(parse_term)(literal).unwrap();
        let gd_literal = {
            let mut gd_literal = literal.to_owned();
            gd_literal.push_str(rest);
            gd_literal
        };
        assert_eq!(
            parse_gd(&gd_literal),
            Ok((rest, GoalDefinition::Literal(literal_ast)))
        );
    }
    // <gd> ::= (and <gd>*)
    {
        let (_, gd_1_ast) = parse_gd(gd_1).unwrap();
        let (_, gd_2_ast) = parse_gd(gd_2).unwrap();
        let gd_and = {
            let mut gd_and = "( and ".to_owned();
            gd_and.push_str(gd_1);
            gd_and.push(' ');
            gd_and.push_str(gd_2);
            gd_and.push_str(" )");
            gd_and.push_str(rest);
            gd_and
        };
        assert_eq!(
            parse_gd(&gd_and),
            Ok((rest, GoalDefinition::And(vec![gd_1_ast, gd_2_ast])))
        );
    }
    // <gd> ::=:disjunctive-preconditions (or <gd>*)
    {
        let (_, gd_1_ast) = parse_gd(gd_1).unwrap();
        let (_, gd_2_ast) = parse_gd(gd_2).unwrap();
        let gd_or = {
            let mut gd_or = "( or ".to_owned();
            gd_or.push_str(gd_1);
            gd_or.push(' ');
            gd_or.push_str(gd_2);
            gd_or.push_str(" )");
            gd_or.push_str(rest);
            gd_or
        };
        assert_eq!(
            parse_gd(&gd_or),
            Ok((rest, GoalDefinition::Or(vec![gd_1_ast, gd_2_ast])))
        );
    }
    // <gd> ::=:disjunctive-preconditions (not <gd>)
    {
        let (_, gd_1_ast) = parse_gd(gd_1).unwrap();
        let gd_not = {
            let mut gd_not = "( not ".to_owned();
            gd_not.push_str(gd_1);
            gd_not.push_str(" )");
            gd_not.push_str(rest);
            gd_not
        };
        assert_eq!(
            parse_gd(&gd_not),
            Ok((rest, GoalDefinition::Not(Box::new(gd_1_ast))))
        );
    }
    // <gd> ::=:disjunctive-preconditions (imply <gd> <gd>)
    {
        let (_, gd_1_ast) = parse_gd(gd_1).unwrap();
        let (_, gd_2_ast) = parse_gd(gd_2).unwrap();
        let gd_imply = {
            let mut gd_imply = "( imply ".to_owned();
            gd_imply.push_str(gd_1);
            gd_imply.push(' ');
            gd_imply.push_str(gd_2);
            gd_imply.push_str(" )");
            gd_imply.push_str(rest);
            gd_imply
        };
        assert_eq!(
            parse_gd(&gd_imply),
            Ok((
                rest,
                GoalDefinition::Imply(Box::new(gd_1_ast), Box::new(gd_2_ast))
            ))
        );
    }
    // <gd> ::=:existential-preconditions
    //     (exists (<typed list (variable)>*) <gd>)
    {
        let (_, gd_1_ast) = parse_gd(gd_1).unwrap();
        let (_, typed_lists_ast) = parse_typed_lists(parse_variable)(typed_lists).unwrap();
        let gd_exists = {
            let mut gd_exists = "( exists ( ".to_owned();
            gd_exists.push_str(typed_lists);
            gd_exists.push_str(" ) ");
            gd_exists.push_str(gd_1);
            gd_exists.push_str(" )");
            gd_exists.push_str(rest);
            gd_exists
        };
        assert_eq!(
            parse_gd(&gd_exists),
            Ok((
                rest,
                GoalDefinition::Exists(vec![typed_lists_ast], Box::new(gd_1_ast))
            ))
        );
    }
    // <gd> ::=:universal-preconditions
    //     (forall (<typed list (variable)>*) <gd>)
    {
        {
            let (_, gd_1_ast) = parse_gd(gd_1).unwrap();
            let (_, typed_lists_ast) = parse_typed_lists(parse_variable)(typed_lists).unwrap();
            let gd_forall = {
                let mut gd_forall = "( forall ( ".to_owned();
                gd_forall.push_str(typed_lists);
                gd_forall.push_str(" ) ");
                gd_forall.push_str(gd_1);
                gd_forall.push_str(" )");
                gd_forall.push_str(rest);
                gd_forall
            };
            assert_eq!(
                parse_gd(&gd_forall),
                Ok((
                    rest,
                    GoalDefinition::ForAll(vec![typed_lists_ast], Box::new(gd_1_ast))
                ))
            );
        }
    }
    // <gd> ::= (= <term> <term>)
    {
        let term_1 = "term_01";
        let term_2 = "term_02";
        let (_, term_1_ast) = parse_term(term_1).unwrap();
        let (_, term_2_ast) = parse_term(term_2).unwrap();
        let gd_eq = {
            let mut gd_eq = "( = ".to_owned();
            gd_eq.push_str(term_1);
            gd_eq.push(' ');
            gd_eq.push_str(term_2);
            gd_eq.push_str(" )");
            gd_eq.push_str(rest);
            gd_eq
        };
        assert_eq!(
            parse_gd(&gd_eq),
            Ok((rest, GoalDefinition::Eq(term_1_ast, term_2_ast)))
        );
    }
}

/**
 * <literal (t)> ::= <atomic formula(t)>
 * <literal (t)> ::= (not <atomic formula(t)>)
 */
#[test]
fn test_literal() {
    let formula = "(pred_01 var_01 var_02)";
    let (_, formula_ast) = parse_atomic_formula(parse_term)(formula).unwrap();

    let eq = {
        let mut eq = formula.to_owned();
        eq.push_str(" rest");
        eq
    };
    let neq = {
        let mut neq = "( not ".to_owned();
        neq.push_str(formula);
        neq.push_str(" )");
        neq.push_str(" rest");
        neq
    };

    assert_eq!(
        parse_literal(parse_term)(&eq),
        Res::Ok((" rest", Literal::Pos(formula_ast)))
    );

    let (_, formula_ast) = parse_atomic_formula(parse_term)(formula).unwrap();
    assert_eq!(
        parse_literal(parse_term)(&neq),
        Res::Ok((" rest", Literal::Neg(formula_ast)))
    );
}

/**
 * <atomic formula(t)> ::= (<predicate> t*)
 */
#[test]
fn test_atomic_formula() {
    assert_eq!(
        parse_atomic_formula(parse_term)("(pred_01 var_01 var_02)rest"),
        Res::Ok((
            "rest",
            AtomicFormula {
                pred: PredicateId { name: "pred_01" },
                elems: vec![Term::Name("var_01"), Term::Name("var_02")]
            }
        ))
    );
}

/**
 * <term> ::= <name>
 * <term> ::= <variable>
 */
#[test]
fn test_term() {
    assert_eq!(
        parse_term("term_1 rest"),
        Res::Ok((" rest", Term::Name("term_1")))
    );
}

#[test]
fn test_p_class() {
    assert_eq!(parse_p_class(":htn"), DefRes::Ok(("", ":htn")));
}

#[test]
fn test_name() {
    assert_eq!(parse_name("test_name12"), DefRes::Ok(("", "test_name12")));

    assert_eq!(
        parse_name("testName hello"),
        DefRes::Ok((" hello", "testName"))
    );

    assert_eq!(
        parse_name(" "),
        Err(NomErr::Error(VerboseError {
            errors: vec![
                (" ", VerboseErrorKind::Nom(ErrorKind::Alpha)),
                (" ", VerboseErrorKind::Context("name"))
            ]
        }))
    )
}
