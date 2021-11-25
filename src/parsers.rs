use nom::{
    branch::alt,
    bytes::complete::{tag, take_while},
    character::complete::{alpha1, alphanumeric1},
    combinator::recognize,
    error::{context, VerboseError},
    multi::{many0, many1},
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult,
};

use crate::syntaxtree::{
    AtomicFormula, BaseType, CEffect, ConstraintDef, Effect, GoalDefinition, Literal, OrderingDef,
    PEffect, Predicate, PredicateId, SubtaskId, Term, Type, TypedList, TypedLists, Types,
    VariableId,
};

// TODO: add whitespace between '(' and labels like ':predicates' or not?
pub type InputType<'input> = &'input str;
pub type Res<I, O> = IResult<I, O, VerboseError<I>>;
pub type IRes<'input, O> = Res<InputType<'input>, O>;

pub fn whitespace(input: &str) -> IRes<&str> {
    let chars = " \t\r\n";
    take_while(move |c| chars.contains(c))(input)
}

/**
 * <types-def> ::= (:types <types>+)
 */
pub fn parse_types_def(input: &str) -> IRes<Vec<Types>> {
    context(
        "types-def",
        delimited(
            tuple((tag("("), whitespace, tag(":types"))),
            many1(preceded(whitespace, parse_types)),
            pair(whitespace, tag(")")),
        ),
    )(input)
}

/**
 * <types> ::= <typed list (name)>
 *     | <base-type>
 */
pub fn parse_types(input: &str) -> IRes<Types> {
    let mut types_list = context("types - list", parse_typed_lists(parse_name));
    let mut types_base = context("types - base", parse_base_type);

    if let Res::Ok((next_input, list)) = types_list(input) {
        Res::Ok((next_input, Types::Subtype(list)))
    } else {
        types_base(input).map(|(next_input, base_type)| (next_input, Types::BaseType(base_type)))
    }
}

/**
 * <base-type> ::= <name>
 */
pub fn parse_base_type(input: &str) -> IRes<BaseType> {
    context("base_type", parse_name)(input)
        .map(|(next_input, name)| (next_input, BaseType { name }))
}

/**
 * <constants-def> ::=
 *     (:constants <typed list (name)>)
 */
pub fn parse_constants_def(input: &str) -> IRes<TypedLists<&str>> {
    context(
        "constants-def",
        delimited(
            tuple((tag("("), whitespace, tag(":constants"), whitespace)),
            parse_typed_lists(parse_name),
            pair(whitespace, tag(")")),
        ),
    )(input)
}

/**
 * <predicates-def> ::=
 *     (:predicates <atomic-formula-skeleton>+)
 */
pub fn parse_predicates_def(input: &str) -> IRes<Vec<Predicate>> {
    context(
        "predicates-def",
        delimited(
            tuple((tag("("), whitespace, tag(":predicates"))),
            many1(preceded(whitespace, parse_atomic_formula_skeleton)),
            pair(whitespace, tag(")")),
        ),
    )(input)
}

/**
 * <atomic-formula-skeleton> ::=
 *     (<predicate> <typed list (variable)>)
 */
pub fn parse_atomic_formula_skeleton(input: &str) -> IRes<Predicate> {
    context(
        "atomic-formula-skeleton",
        delimited(
            pair(tag("("), whitespace),
            pair(
                terminated(parse_predicate, whitespace),
                parse_typed_lists(parse_variable),
            ),
            pair(whitespace, tag(")")),
        ),
    )(input)
    .map(|(next_input, (predicate, parameters))| {
        (
            next_input,
            Predicate {
                predicate,
                parameters,
            },
        )
    })
}

/**
 * <predicate> ::= <name>
 */
pub fn parse_predicate(input: &str) -> IRes<PredicateId> {
    context("predicate", parse_name)(input)
        .map(|(next_input, name)| (next_input, PredicateId { name }))
}

/**
 * <variable> ::= ?<name>
 * TODO: why is a variable an optional name? To me this does not make sense right now, as a result expect a definite name
 *  and wrap it into an optional to satisfy the interface.
 *  Ask Behnke et al what the idea here is
 */
pub fn parse_variable(input: &str) -> IRes<VariableId> {
    context("variable", parse_name)(input)
        .map(|(next_input, name)| (next_input, VariableId { name: Some(name) }))
}

/**
 * <typed list (x)> ::= x+ - <type>
 *     [<typed list (x)>]
 */
pub fn parse_typed_lists<'input, F, O>(f: F) -> impl FnMut(&'input str) -> IRes<TypedLists<O>>
where
    F: FnMut(&'input str) -> IRes<O>,
{
    let typed_list = pair(
        terminated(many1(terminated(f, whitespace)), pair(tag("-"), whitespace)),
        parse_type,
    );

    let mut typed_lists = context("typed list", many1(terminated(typed_list, whitespace)));

    move |input: &str| {
        typed_lists(input).map(|(next_input, elems)| {
            (
                next_input,
                TypedLists {
                    elems: elems
                        .into_iter()
                        .map(|(elems, elem_type)| TypedList { elems, elem_type })
                        .collect(),
                },
            )
        })
    }
}

/**
 * <primitive-type> ::= <name>
 */
pub fn parse_primitive_type(input: &str) -> IRes<&str> {
    context("primitive-type", parse_name)(input)
}

/**
 * <type> ::= (either <primitive-type>+)
 * <type> ::= <primitive-type>
 */
pub fn parse_type(input: &str) -> IRes<Type> {
    let mut list = delimited(
        tuple((tag("("), whitespace, tag("either"), whitespace)),
        many1(terminated(parse_primitive_type, whitespace)),
        tag(")"),
    );
    let single = parse_primitive_type;

    if let Ok((next_input, elems)) = list(input) {
        Ok((next_input, Type::List(elems)))
    } else {
        single(input).map(|(next_input, type_id)| (next_input, Type::Single(type_id)))
    }
}

/**
 * <subtask-id> ::= <name>
 */
pub fn parse_subtask_id(input: &str) -> IRes<SubtaskId> {
    context("subtask-id", parse_name)(input)
        .map(|(next_input, name)| (next_input, SubtaskId { name }))
}

/**
 * <ordering-defs> ::= () | <ordering-def>
 *     | (and <ordering-def>+)
 */
pub fn parse_ordering_defs(input: &str) -> IRes<Vec<OrderingDef>> {
    let def_empty = tag("()");
    let def_single = parse_ordering_def;
    let mut def_list = delimited(
        tuple((tag("("), whitespace, tag("and"))),
        many1(preceded(whitespace, parse_ordering_def)),
        pair(whitespace, tag(")")),
    );

    if let IRes::Ok((next_input, _)) = def_empty(input) {
        IRes::Ok((next_input, vec![]))
    } else if let IRes::Ok((next_input, def)) = def_single(input) {
        IRes::Ok((next_input, vec![def]))
    } else {
        def_list(input)
    }
}

/**
 * <ordering-def> ::=
 *     (<subtask-id> "<" <subtask-id>)
 */
pub fn parse_ordering_def(input: &str) -> IRes<OrderingDef> {
    context(
        "ordering-def",
        delimited(
            pair(tag("("), whitespace),
            pair(
                terminated(parse_subtask_id, tuple((whitespace, tag("<"), whitespace))),
                parse_subtask_id,
            ),
            pair(whitespace, tag(")")),
        ),
    )(input)
    .map(|(next_input, (first, second))| (next_input, OrderingDef { first, second }))
}

/**
 * <constraint-defs> ::= () | <constraint-def>
 *     | (and <constraint-def>+)
 */
pub fn parse_constraint_defs(input: &str) -> IRes<Vec<ConstraintDef>> {
    let mut list = delimited(
        tuple((tag("("), whitespace, tag("and"), whitespace)),
        many1(pair(parse_constraint_def, whitespace)),
        tag(")"),
    );

    if let Ok((next_input, _)) = tuple((tag("("), whitespace, tag(")")))(input) {
        Ok((next_input, vec![]))
    } else if let Ok((next_input, def)) = parse_constraint_def(input) {
        if let Some(def) = def {
            Ok((next_input, vec![def]))
        } else {
            Ok((next_input, vec![]))
        }
    } else {
        list(input).map(|(next_input, defs)| {
            (
                next_input,
                defs.into_iter().map(|(def, _)| def).flatten().collect(),
            )
        })
    }
}

/**
 * <constraint-def> ::= ()
 *     | (not (= <term> <term>))
 *     | (= <term> <term>)
 */
pub fn parse_constraint_def(input: &str) -> IRes<Option<ConstraintDef>> {
    let mut eq = delimited(
        tuple((tag("("), whitespace, tag("="), whitespace)),
        pair(terminated(parse_term, whitespace), parse_term),
        pair(whitespace, tag(")")),
    );
    let mut neq = {
        let eq = delimited(
            tuple((tag("("), whitespace, tag("="), whitespace)),
            pair(terminated(parse_term, whitespace), parse_term),
            pair(whitespace, tag(")")),
        );
        delimited(
            tuple((tag("("), whitespace, tag("not"), whitespace)),
            eq,
            pair(whitespace, tag(")")),
        )
    };

    if let Ok((next_input, (t1, t2))) = neq(input) {
        Ok((next_input, Some(ConstraintDef::NEq(t1, t2))))
    } else if let Ok((next_input, (t1, t2))) = eq(input) {
        Ok((next_input, Some(ConstraintDef::Eq(t1, t2))))
    } else {
        tuple((tag("("), whitespace, tag(")")))(input).map(|(next_input, _)| (next_input, None))
    }
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
pub fn parse_gd<'input>(input: &'input str) -> IRes<GoalDefinition> {
    let empty = |input: &'input str| {
        tuple((tag("("), whitespace, tag(")")))(input)
            .map(|(next_input, _)| (next_input, GoalDefinition::Empty))
    };
    let formula = |input: &'input str| {
        parse_atomic_formula(parse_term)(input)
            .map(|(next_input, formula)| (next_input, GoalDefinition::Formula(formula)))
    };
    let literal = |input: &'input str| {
        parse_literal(parse_term)(input)
            .map(|(next_input, literal)| (next_input, GoalDefinition::Literal(literal)))
    };
    let and = |input: &'input str| {
        delimited(
            tuple((tag("("), whitespace, tag("and"), whitespace)),
            many0(terminated(parse_gd, whitespace)),
            tag(")"),
        )(input)
        .map(|(next_input, gds)| (next_input, GoalDefinition::And(gds)))
    };
    let or = |input: &'input str| {
        delimited(
            tuple((tag("("), whitespace, tag("or"), whitespace)),
            many0(terminated(parse_gd, whitespace)),
            tag(")"),
        )(input)
        .map(|(next_input, gds)| (next_input, GoalDefinition::Or(gds)))
    };
    let not = |input: &'input str| {
        delimited(
            tuple((tag("("), whitespace, tag("not"), whitespace)),
            parse_gd,
            pair(whitespace, tag(")")),
        )(input)
        .map(|(next_input, gd)| (next_input, GoalDefinition::Not(Box::new(gd))))
    };
    let imply = |input: &'input str| {
        delimited(
            tuple((tag("("), whitespace, tag("imply"), whitespace)),
            pair(terminated(parse_gd, whitespace), parse_gd),
            pair(whitespace, tag(")")),
        )(input)
        .map(|(next_input, (gd_1, gd_2))| {
            (
                next_input,
                GoalDefinition::Imply(Box::new(gd_1), Box::new(gd_2)),
            )
        })
    };
    let exists = |input: &'input str| {
        delimited(
            tuple((
                tag("("),
                whitespace,
                tag("exists"),
                whitespace,
                tag("("),
                whitespace,
            )),
            pair(
                many0(terminated(parse_typed_lists(parse_variable), whitespace)),
                preceded(pair(tag(")"), whitespace), parse_gd),
            ),
            pair(whitespace, tag(")")),
        )(input)
        .map(|(next_input, (vars, gd))| (next_input, GoalDefinition::Exists(vars, Box::new(gd))))
    };
    let forall = |input: &'input str| {
        delimited(
            tuple((
                tag("("),
                whitespace,
                tag("forall"),
                whitespace,
                tag("("),
                whitespace,
            )),
            pair(
                many0(terminated(parse_typed_lists(parse_variable), whitespace)),
                preceded(pair(tag(")"), whitespace), parse_gd),
            ),
            pair(whitespace, tag(")")),
        )(input)
        .map(|(next_input, (vars, gd))| (next_input, GoalDefinition::ForAll(vars, Box::new(gd))))
    };
    let eq = |input: &'input str| {
        delimited(
            tuple((tag("("), whitespace, tag("="), whitespace)),
            pair(parse_term, preceded(whitespace, parse_term)),
            pair(whitespace, tag(")")),
        )(input)
        .map(|(next_input, (t1, t2))| (next_input, GoalDefinition::Eq(t1, t2)))
    };

    context(
        "goal definition",
        alt((
            context("gd empty", empty),
            context("gd formula", formula),
            context("gd literal", literal),
            context("gd and", and),
            context("gd or", or),
            context("gd not", not),
            context("gd imply", imply),
            context("gd exists", exists),
            context("gd forall", forall),
            context("gd eq", eq),
        )),
    )(input)
}

/**
 * <literal (t)> ::= <atomic formula(t)>
 * <literal (t)> ::= (not <atomic formula(t)>)
 */
pub fn parse_literal<'input, F, O>(f: F) -> impl FnMut(&'input str) -> IRes<Literal<O>>
where
    F: FnMut(&'input str) -> IRes<O>,
{
    let mut formula = delimited(
        pair(tag("("), whitespace),
        pair(parse_predicate, many0(preceded(whitespace, f))),
        pair(whitespace, tag(")")),
    );

    move |input: &str| {
        if let Ok((next_input, _)) = context(
            "literal - not-prefix",
            tuple((tag("("), whitespace, tag("not"), whitespace)),
        )(input)
        {
            let res: IRes<Literal<O>> = formula(next_input).map(|(next_input, (pred, elems))| {
                (next_input, Literal::Neg(AtomicFormula { pred, elems }))
            });
            match res {
                Ok((next_input, lit)) => {
                    context("literal - not suffix", pair(whitespace, tag(")")))(next_input)
                        .map(|(next_input, _)| (next_input, lit))
                }
                Err(e) => Err(e),
            }
        } else {
            formula(input).map(|(next_input, (pred, elems))| {
                (next_input, Literal::Pos(AtomicFormula { pred, elems }))
            })
        }
    }
}

/**
 * <atomic formula(t)> ::= (<predicate> t*)
 */
pub fn parse_atomic_formula<'input, F, O>(f: F) -> impl FnMut(&'input str) -> IRes<AtomicFormula<O>>
where
    F: FnMut(&'input str) -> IRes<O>,
{
    let mut formula = delimited(
        pair(tag("("), whitespace),
        pair(parse_predicate, many0(preceded(whitespace, f))),
        pair(whitespace, tag(")")),
    );

    move |input: &str| {
        formula(input)
            .map(|(next_input, (pred, elems))| (next_input, AtomicFormula { pred, elems }))
    }
}

/**
 * <term> ::= <name>
 * <term> ::= <variable>
 */
pub fn parse_term(input: &str) -> IRes<Term> {
    if let Ok((next_input, name)) = parse_name(input) {
        IRes::Ok((next_input, Term::Name(name)))
    } else {
        parse_variable(input).map(|(next_input, var)| (next_input, Term::Var(var)))
    }
}

/**
 * <effect> ::= ()
 * <effect> ::= (and <c-effect>*)
 * <effect> ::= <c-effect>
 */
pub fn parse_effect<'input>(input: &'input str) -> IRes<Effect> {
    let empty_effect = |input: &'input str| {
        tuple((tag("("), whitespace, tag(")")))(input)
            .map(|(next_input, _)| (next_input, Vec::<CEffect>::new()))
    };

    let and_effect = |input: &'input str| {
        context(
            "and effect",
            delimited(
                tuple((tag("("), whitespace, tag("and"), whitespace)),
                many0(terminated(parse_c_effect, whitespace)),
                tag(")"),
            ),
        )(input)
    };

    let single_effect = |input: &'input str| {
        context("single effect", parse_c_effect)(input)
            .map(|(next_input, ceffect)| (next_input, vec![ceffect]))
    };

    context("effect", alt((empty_effect, and_effect, single_effect)))(input)
        .map(|(next_input, ceffects)| (next_input, Effect { ceffects }))
}

/**
 * <c-effect> ::=:conditional-effects
 *     (forall (<variable>*) <effect>)
 * <c-effect> ::=:conditional-effects
 *     (when <gd> <cond-effect>)
 * <c-effect> ::= <p-effect>
 */
pub fn parse_c_effect<'input>(input: &'input str) -> IRes<CEffect> {
    let forall_c_effect = |input: &'input str| {
        context(
            "forall c-effect",
            delimited(
                tuple((
                    tag("("),
                    whitespace,
                    tag("forall"),
                    whitespace,
                    tag("("),
                    whitespace,
                )),
                pair(
                    many0(terminated(parse_variable, whitespace)),
                    preceded(pair(tag(")"), whitespace), parse_effect),
                ),
                pair(whitespace, tag(")")),
            ),
        )(input)
        .map(|(next_input, (variables, effect))| {
            (next_input, CEffect::ForAll(variables, Box::new(effect)))
        })
    };

    let when_c_effect = |input: &'input str| {
        context(
            "when c-effect",
            delimited(
                tuple((tag("("), whitespace, tag("when"), whitespace)),
                pair(terminated(parse_gd, whitespace), parse_cond_effect),
                pair(whitespace, tag(")")),
            ),
        )(input)
        .map(|(next_input, (gd, p_effects))| (next_input, CEffect::When(gd, p_effects)))
    };

    let single_c_effect = |input: &'input str| {
        context("single c-effect", parse_p_effect)(input)
            .map(|(next_input, peffect)| (next_input, CEffect::Single(peffect)))
    };

    context(
        "c-effect",
        alt((forall_c_effect, when_c_effect, single_c_effect)),
    )(input)
}

/**
 * <p-effect> ::= (not <atomic formula(term)>)
 * <p-effect> ::= <atomic formula(term)>
 */
pub fn parse_p_effect<'input>(input: &'input str) -> IRes<PEffect> {
    let not_p_effect = |input: &'input str| {
        context(
            "not p-effect",
            delimited(
                tuple((tag("("), whitespace, tag("not"), whitespace)),
                parse_atomic_formula(parse_term),
                pair(whitespace, tag(")")),
            ),
        )(input)
        .map(|(next_input, effect)| (next_input, PEffect::Not(effect)))
    };

    let yes_p_effect = |input: &'input str| {
        context("yes p-effect", parse_atomic_formula(parse_term))(input)
            .map(|(next_input, effect)| (next_input, PEffect::Yes(effect)))
    };

    context("p-effect", alt((not_p_effect, yes_p_effect)))(input)
}

/**
 * <cond-effect> ::= (and <p-effect>*)
 * <cond-effect> ::= <p-effect>
 */
pub fn parse_cond_effect<'input>(input: &'input str) -> IRes<Vec<PEffect>> {
    let list_cond_effect = context(
        "list cond-effect",
        delimited(
            tuple((tag("("), whitespace, tag("and"), whitespace)),
            many0(terminated(parse_p_effect, whitespace)),
            tag(")"),
        ),
    );

    let single_cond_effect = |input: &'input str| {
        context("single cond-effect", parse_p_effect)(input)
            .map(|(next_input, effect)| (next_input, vec![effect]))
    };

    context("cond-effect", alt((list_cond_effect, single_cond_effect)))(input)
}

pub fn parse_p_class(input: &str) -> IRes<&str> {
    context("p_class", tag(":htn"))(input)
}

/**
 * Assume a name is:
 *  any character followed by
 *  a string of characters, digits, - and _
 */
pub fn parse_name(input: &str) -> IRes<&str> {
    context(
        "name",
        recognize(pair(
            alpha1,
            many0(alt((alphanumeric1, tag("-"), tag("_")))),
        )),
    )(input)
}
