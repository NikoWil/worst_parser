/**
 * <types> ::= <typed list (name)>
 *     | <base-type>
 */
#[derive(Debug, PartialEq, Eq)]
pub enum Types<'input> {
    Subtype(TypedLists<'input, &'input str>),
    BaseType(BaseType<'input>),
}

/**
 * <base-type> ::= <name>
 */
#[derive(Debug, PartialEq, Eq)]
pub struct BaseType<'input> {
    pub name: &'input str,
}

/**
 * <atomic-formula-skeleton> ::=
 *     (<predicate> <typed list (variable)>)
 */
#[derive(Debug, PartialEq, Eq)]
pub struct Predicate<'input> {
    pub predicate: PredicateId<'input>,
    pub parameters: TypedLists<'input, VariableId<'input>>,
}

/**
 * <predicate> ::= <name>
 */
#[derive(Debug, PartialEq, Eq)]
pub struct PredicateId<'input> {
    pub name: &'input str,
}

/**
 * <variable> ::= ?<name>
 */
#[derive(Debug, PartialEq, Eq)]
pub struct VariableId<'input> {
    pub name: Option<&'input str>,
}

/**
 * <typed list (x)> ::= x+ - <type>
 *     [<typed list (x)>]
 */
#[derive(Debug, PartialEq, Eq)]
pub struct TypedLists<'input, O> {
    pub elems: Vec<TypedList<'input, O>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypedList<'input, O> {
    pub elems: Vec<O>,
    pub elem_type: Type<'input>,
}

/**
 * <type> ::= (either <primitive-type>+)
 * <type> ::= <primitive-type>
 */
#[derive(Debug, PartialEq, Eq)]
pub enum Type<'input> {
    Single(&'input str),
    List(Vec<&'input str>),
}

/**
 * <subtask-id> ::= <name>
 */
pub struct SubtaskId<'input> {
    pub name: &'input str,
}

/**
 * <ordering-def> ::=
 *     (<subtask-id> "<" <subtask-id>)
 */
pub struct OrderingDef<'input> {
    pub first: SubtaskId<'input>,
    pub second: SubtaskId<'input>,
}
