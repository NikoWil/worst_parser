use nom::{
    error::{ErrorKind, VerboseError, VerboseErrorKind},
    Err as NomErr,
};
use worst_parser::{parsers::{Res, parse_atomic_formula_skeleton, parse_constants_def, parse_name, parse_p_class, parse_predicate, parse_predicates_def, parse_variable}, syntaxtree::{Predicate, PredicateId, TypedList}};
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
                                VariableId { name: Some("foo") },
                                VariableId { name: Some("bar") },
                                VariableId { name: Some("baz") }
                            ]
                        },
                        TypedList {
                            elem_type: Type::Single("box"),
                            elems: vec![
                                VariableId { name: Some("x") },
                                VariableId { name: Some("y") },
                                VariableId { name: Some("z") }
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
                    elems: vec![
                        TypedList {
                            elem_type: Type::List(vec!["object", "box", "tree"]),
                            elems: vec![
                                VariableId { name: Some("foo") },
                                VariableId { name: Some("bar") },
                                VariableId { name: Some("baz") }
                            ]
                        },
                    ]
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
                        VariableId { name: Some("a") },
                        VariableId { name: Some("b") },
                        VariableId { name: Some("c") }
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
                            VariableId { name: Some("a") },
                            VariableId { name: Some("b") },
                            VariableId { name: Some("c") }
                        ],
                        elem_type: Type::Single("object")
                    },
                    TypedList {
                        elems: vec![
                            VariableId { name: Some("d") },
                            VariableId { name: Some("e") },
                            VariableId { name: Some("f") }
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
                        VariableId { name: Some("a") },
                        VariableId { name: Some("b") },
                        VariableId { name: Some("c") }
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
