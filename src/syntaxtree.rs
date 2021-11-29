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
    pub name: &'input str,
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
 * <tasknetwork-def> ::=
 *     [:[ordered-][sub]tasks
 *         <subtask-defs>]
 *     [:order[ing] <ordering-defs>]
 *     [:constraints <constraint-defs>]
 */
#[derive(Debug, PartialEq, Eq)]
pub struct TasknetworkDef<'input> {
    pub subtasks: OrderedSubtasks<'input>,
    pub constraints: Vec<ConstraintDef<'input>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum OrderedSubtasks<'input> {
    Total(Vec<SubtaskDef<'input>>),
    Partial(Vec<SubtaskDef<'input>>, Vec<OrderingDef<'input>>),
}

/**
 * <subtask-def> ::= (<task-symbol> <term>*)
 *     | (<subtask-id> (<task-symbol> <term>*))
 */
#[derive(Debug, PartialEq, Eq)]
pub struct SubtaskDef<'input> {
    pub id: Option<SubtaskId<'input>>,
    pub symbol: &'input str,
    pub variables: Vec<Term<'input>>,
}

/**
 * <subtask-id> ::= <name>
 */
#[derive(Debug, PartialEq, Eq)]
pub struct SubtaskId<'input> {
    pub name: &'input str,
}

/**
 * <ordering-def> ::=
 *     (<subtask-id> "<" <subtask-id>)
 */
#[derive(Debug, PartialEq, Eq)]
pub struct OrderingDef<'input> {
    pub first: SubtaskId<'input>,
    pub second: SubtaskId<'input>,
}

/**
 * <constraint-def> ::= ()
 *     | (not (= <term> <term>))
 *     | (= <term> <term>)
 */
#[derive(Debug, PartialEq, Eq)]
pub enum ConstraintDef<'input> {
    Eq(Term<'input>, Term<'input>),
    NEq(Term<'input>, Term<'input>),
}

/**
 * <action-def> ::= (:action <task-def>
 *     [:precondition <gd>]
 *     [:effects <effect>])
 */
#[derive(Debug, PartialEq, Eq)]
pub struct ActionDef<'input> {
    pub task_def: &'input str,
    pub precondition: Option<GoalDefinition<'input>>,
    pub effects: Option<Effect<'input>>,
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
#[derive(Debug, PartialEq, Eq)]
pub enum GoalDefinition<'input> {
    Empty,
    Formula(AtomicFormula<'input, Term<'input>>),
    Literal(Literal<'input, Term<'input>>),
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
    Eq(Term<'input>, Term<'input>),
}

/**
 * <literal (t)> ::= <atomic formula(t)>
 * <literal (t)> ::= (not <atomic formula(t)>)
 */
#[derive(Debug, PartialEq, Eq)]
pub enum Literal<'input, T> {
    Pos(AtomicFormula<'input, T>),
    Neg(AtomicFormula<'input, T>),
}

/**
 * <atomic formula(t)> ::= (<predicate> t*)
 */
#[derive(Debug, PartialEq, Eq)]
pub struct AtomicFormula<'input, T> {
    pub pred: PredicateId<'input>,
    pub elems: Vec<T>,
}

/**
 * <term> ::= <name>
 * <term> ::= <variable>
 */
#[derive(Debug, PartialEq, Eq)]
pub enum Term<'input> {
    Name(&'input str),
    Var(VariableId<'input>),
}

/**
 * <effect> ::= ()
 * <effect> ::= (and <c-effect>*)
 * <effect> ::= <c-effect>
 */
#[derive(Debug, PartialEq, Eq)]
pub struct Effect<'input> {
    pub ceffects: Vec<CEffect<'input>>,
}

/**
 * <c-effect> ::=:conditional-effects
 *     (forall (<variable>*) <effect>)
 * <c-effect> ::=:conditional-effects
 *     (when <gd> <cond-effect>)
 * <c-effect> ::= <p-effect>
 */
#[derive(Debug, PartialEq, Eq)]
pub enum CEffect<'input> {
    ForAll(Vec<VariableId<'input>>, Box<Effect<'input>>),
    When(GoalDefinition<'input>, Vec<PEffect<'input>>),
    Single(PEffect<'input>),
}

/**
 * <p-effect> ::= (not <atomic formula(term)>)
 * <p-effect> ::= <atomic formula(term)>
 */
#[derive(Debug, PartialEq, Eq)]
pub enum PEffect<'input> {
    Yes(AtomicFormula<'input, Term<'input>>),
    Not(AtomicFormula<'input, Term<'input>>),
}
