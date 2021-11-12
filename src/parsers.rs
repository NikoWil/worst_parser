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
    BaseType, OrderingDef, Predicate, PredicateId, SubtaskId, Type, TypedList, TypedLists, Types,
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
pub fn parse_typed_lists<'input, F, O>(
    f: F,
) -> impl FnMut(&'input str) -> IRes<TypedLists<'input, O>>
where
    F: FnMut(&'input str) -> IRes<'input, O> + 'input,
    O: 'input,
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
            pair(tag(")"), whitespace),
        ),
    )(input)
    .map(|(next_input, (first, second))| (next_input, OrderingDef { first, second }))
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
