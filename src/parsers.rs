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
    AtomicFormula, BaseType, ConstraintDef, GoalDefinition, Literal, OrderingDef, Predicate,
    PredicateId, SubtaskId, Term, Type, TypedList, TypedLists, Types, VariableId,
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
    /*Literal(Literal<'input, Term<'input>>),
    And(Vec<GoalDefinition<'input>>),
    Or(Vec<GoalDefinition<'input>>),
    Not(Box<GoalDefinition<'input>>),
    Imply(Box<GoalDefinition<'input>>, Box<GoalDefinition<'input>>),
    Exists(
        Vec<TypedLists<'input, VariableId<'input>>>,
        Box<GoalDefinition<'input>>,
    ),
    ForAll(
        Vec<TypedLists<'input, VariableId<'input>>>,
        Box<GoalDefinition<'input>>,
    ),
    Eq(Term<'input>, Term<'input>),*/
    let empty = |input: &'input str| {
        tuple((tag("("), whitespace, tag(")")))(input)
            .map(|(next_input, _)| (next_input, GoalDefinition::Empty))
    };
    let formula = |input: &'input str| {
        parse_atomic_formula(parse_term)(input)
            .map(|(next_input, formula)| (next_input, GoalDefinition::Formula(formula)))
    };
    let literal = |input: &str| {};

    panic!();
}

/* fn gd_literal(input: &str) -> IRes<GoalDefinition> {
    parse_literal(input, &parse_term)
            .map(|(next_input, literal)| (next_input, GoalDefinition::Literal(literal)))
}

/**
 * <literal (t)> ::= <atomic formula(t)>
 * <literal (t)> ::= (not <atomic formula(t)>)
 */
//TODO: make this interface nicer, like parse_typed_lists and parse_atomic_formula
pub fn parse_literal<'input, O>(
    input: &'input str,
    f: &'static dyn Fn(&str) -> Res<&str, O>,
) -> IRes<'input, Literal<'input, O>>
where
{
    alt((
        |input: &'input str| {
            parse_atomic_formula(f)(input)
                .map(|(next_input, formula)| (next_input, Literal::Pos(formula)))
        },
        |input: &'input str| {
            delimited(
                tuple((tag("("), whitespace, tag("not"), whitespace)),
                parse_atomic_formula(f),
                pair(whitespace, tag(")")),
            )(input)
            .map(|(next_input, formula)| (next_input, Literal::Pos(formula)))
        },
    ))(input)
} */

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
