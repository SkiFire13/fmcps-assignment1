import pynusmv
import sys

from collections import deque

from typing import Literal, Optional

from pynusmv.dd import BDD, State
from pynusmv.fsm import BddFsm
from pynusmv.prop import Spec

from pynusmv_lower_interface.nusmv.parser import parser

specTypes = {
    'LTLSPEC': parser.TOK_LTLSPEC,
    'CONTEXT': parser.CONTEXT,

    'IMPLIES': parser.IMPLIES,
    'IFF': parser.IFF,
    'OR': parser.OR,
    'XOR': parser.XOR,
    'XNOR': parser.XNOR,
    'AND': parser.AND,
    'NOT': parser.NOT,

    'ATOM': parser.ATOM,
    'NUMBER': parser.NUMBER,
    'DOT': parser.DOT,

    'NEXT': parser.OP_NEXT,
    'OP_GLOBAL': parser.OP_GLOBAL,
    'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,

    'EQUAL': parser.EQUAL,
    'NOTEQUAL': parser.NOTEQUAL,
    'LT': parser.LT,
    'GT': parser.GT,
    'LE': parser.LE,
    'GE': parser.GE,

    'TRUE': parser.TRUEEXP,
    'FALSE': parser.FALSEEXP
}

basicTypes = {
    parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT,
    parser.EQUAL, parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE
}
booleanOp = { parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF }

def spec_to_bdd(model: BddFsm, spec: Spec) -> BDD:
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`.
    The `model` is a symbolic representation of the loaded smv program that can be
    obtained with `pynusmv.glob.prop_database().master.bddFsm`.
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec

def is_boolean_formula(spec: Spec) -> bool:
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators.
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False

def parse_GF_formula(spec: Spec) -> Optional[Spec]:
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f is a
    boolean combination of base formulas with no temporal operators.
    Returns `f` if `spec` is in the correct form, None otherwise
    """
    # check if formula is of type GF f_i
    if spec.type != specTypes['OP_GLOBAL']:
        return None
    spec = spec.car
    if spec.type != specTypes['OP_FUTURE']:
        return None
    spec = spec.car
    if not is_boolean_formula(spec):
        return None
    return spec

def parse_implication(spec: Spec) -> Optional[tuple[Spec, Spec]]:
    """
    Visit the syntactic tree of the formula `spec` to check if it is a simple
    reactivity formula, that is wether the formula is of the form

                    GF f -> GF g

    where f and g are boolean combination of basic formulas.
    """
    # the root of a reactive formula should be of type IMPLIES
    if spec.type != specTypes['IMPLIES']:
        return None
    # Parse the lhs as a GF formula.
    lhs = parse_GF_formula(spec.car)
    if lhs is None:
        return None
    # Parse the rhs as a GF formula.
    rhs = parse_GF_formula(spec.cdr)
    if rhs is None:
        return None
    return lhs, rhs

def parse_react(spec: Spec) -> Optional[list[tuple[Spec, Spec]]]:
    """
    Visit the syntactic tree of the formula `spec` to check if it is a Reactivity
    formula, that is wether the formula is of the form

        (GF f_1 -> GF g_1) & ... & (GF f_n -> GF g_n)

    where f_1, ..., f_n, g_1, ..., g_n are boolean combination of basic formulas.

    Returns a list of tuples (f_i, g_i) if `spec` is a Reactivity formula, None otherwise.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # check all conjuncts of the main formula
    working = deque()
    working.append(spec)
    # this holds the (f_i, g_i)s that will be returned on success
    implications = []
    while working:
        # next formula to analyse
        head = working.pop()
        if head.type == specTypes['AND']:
            # push conjuncts into the queue
            working.append(head.car)
            working.append(head.cdr)
        else:
            # check if it is a GF f -> GF g formula
            implication = parse_implication(head)
            if implication is None:
                return None
            implications.append(implication)
    # if we are here, all conjuncts are of the correct form
    return implications

def reachable_bdd(model: BddFsm) -> BDD:
    """
    Returns the set of `model`'s reachable states as a BDD
    and computed through symbolic execution.
    """
    reach = model.init
    new = model.init
    while new.isnot_false():
        new = model.post(new) - reach
        reach = reach + new
    return reach

def repeatedly(model: BddFsm, spec: Spec) -> bool:
    """
    Returns whether the given `model` satisfies `spec` repeatedly.
    """
    bddspec = spec_to_bdd(model, spec)
    reach = reachable_bdd(model)
    # We start from the set of reachable states that satisfy `spec`.
    recur = reach & bddspec
    while recur.isnot_false():
        # We iteratively compute `prereach`, the set of states that
        # can reach recur in at least 1 step, by repeatedly applying `pre`.
        prereach = BDD.false()
        new = model.pre(recur)
        while new.isnot_false():
            prereach = prereach + new
            # Since we'll update `recur` by intersecting it with
            # prereach, if `recur` is included in `prereach` we can
            # already conclude that it won't change, and hence there is a cycle.
            # Thus return True.
            if recur.entailed(prereach):
                return True
            new = model.pre(new) - prereach
        recur = recur & prereach
    # If `recur` became empty then it means there's no cycle and so
    # `spec` can't be true repeatedly. Hence return False.
    return False

def find_repeating_state(model: BddFsm, recur: BDD) -> State:
    """
    Returns a repeating state, that is a state that can be visited repeatedly,
    given the `model` and the set `recur` of states that satisfy `spec` and
    can be reached starting from itself. 
    """
    # TODO: Verify this algorithm or change it to the one given by the professor.
    while True:
        postreach = BDD.false()
        new = model.post(recur)
        while new.isnot_false():
            postreach = postreach + new
            if recur.entailed(postreach):
                return model.pick_one_state(recur)
            new = model.post(postreach) - postreach
        recur = recur & postreach

def execution_from_frontiers(model: BddFsm, frontiers: list[BDD], goal: State) -> list[State]:
    """
    Builds an execution until the state `goal` given a set of frontiers used
    while trying to reach it from some set of states.
    """
    # We build `execution` by working out way back from `goal`.
    last = goal
    execution = [goal]
    for frontier in reversed(frontiers):
        # We compute the set of states that can reach `last`
        # and are in the frontier being considered.
        candidates = model.pre(last) & frontier
        # There is surely at least one candidate because `frontier`
        # was built in such a way that each set of states can reach the next one,
        # and `last` is part of that next one.
        # There could however be more than one candidate, so pick one.
        state = model.pick_one_state(candidates)
        execution.append(state)
        last = state
    # We built `execution` in reverse, from the last until the first,
    # so we need to reverse it to get the correct execution order.
    execution.reverse()
    return execution

def find_execution(model: BddFsm, start: BDD, goal: State) -> list[State]:
    """
    Finds an execution from a state in the given set of states `start` until the state `goal`.
    """
    # TODO: this is essentially recomputing reach but until goal
    #       Can I reuse a set of frontiers from the initial reach calculation?
    reach = start
    new = start
    frontiers = []
    while new.isnot_false():
        if goal.entailed(new):
            return execution_from_frontiers(model, frontiers, goal)
        frontiers.append(new)
        new = model.post(new) - reach
        reach = reach + new
    raise "Execution doesn't exist"

def execution_to_explanation(model: BddFsm, execution: list[State]) -> list[dict[str, str]]:
    """
    Create a textual explanation of a given execution, that is a list of
    alternating (textual) states and inputs that match the given symbolic states.
    """
    # Start with the initial state.
    # At every step will add the inputs to get to the next state and that state itself.
    explanation = [execution[0].get_str_values()]
    # Loop over sliding windows of size 2, that is for each state and the next one.
    for s1, s2 in zip(execution, execution[1:]):
        # Compute the possible inputs to go from one state to the other
        # and pick one of them.
        inputs = model.get_inputs_between_states(s1, s2)
        input = model.pick_one_inputs(inputs)
        # Then add their textual representation to the list.
        explanation.append(input.get_str_values())
        explanation.append(s2.get_str_values())
    return explanation

def build_explanation(model: BddFsm, recur: BDD) -> list[dict[str, str]]:
    """
    Returns an explanation of how `model` can repeatedly visit the `recur` set of states.
    """
    # First find a state that can actually be visited repeatedly,
    s = find_repeating_state(model, recur)
    # Then build the execution from the initial state until s
    reach_execution = find_execution(model, model.init, s)
    # Then build the execution from post(s) until s.
    # Note: an execution from s to s would be simply made by s,
    # hence we need to start from post(s). Also, `reach_execution`
    # already ends in `s`.
    loop_execution = find_execution(model, model.post(s), s)
    # Finally convert the execution to an explanation.
    return execution_to_explanation(model, reach_execution + loop_execution)

def repeatedly_explain(model: BddFsm, spec: Spec) -> tuple[Literal[True], list[BDD]] | tuple[Literal[False], None]:
    """
    Returns whether the given `model` satisfies `spec` repeatedly.
    Returns also an explanation for why the model satisfies `spec`, if it is the case.
    """
    bddspec = spec_to_bdd(model, spec)
    reach = reachable_bdd(model)
    # We start from the set of reachable states that satisfy `spec`.
    recur = reach & bddspec
    while recur.isnot_false():
        # We iteratively compute `prereach`, the set of states that
        # can reach recur in at least 1 step, by repeatedly applying `pre`.
        prereach = BDD.false()
        new = model.pre(recur)
        while new.isnot_false():
            prereach = prereach + new
            # Since we'll update `recur` by intersecting it with
            # prereach, if `recur` is included in `prereach` we can
            # already conclude that it won't change, and hence there is a cycle.
            # Thus return True and build an explanation for it.
            if recur.entailed(prereach):
                return True, build_explanation(model, recur)
            new = model.pre(new) - prereach
        recur = recur & prereach
    # If `recur` became empty then it means there's no cycle and so
    # `spec` can't be true repeatedly. Hence return False.
    return False, None

def check_explain_react_spec(spec: Spec) -> Optional[tuple[Literal[True], None] | tuple[Literal[False], list[BDD]]]:
    """
    Returns whether the loaded SMV model satisfies or not the reactivity formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. Returns also an explanation for why the model does not satisfy
    `spec`, if it is the case.

    The result is `None` if `spec` is not a reactivity formula, otherwise it is a
    tuple where the first element is a boolean telling whether `spec` is satisfied,
    and the second element is either `None` if the first element is `True`, or an execution
    of the SMV model violating `spec` otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ending with a state. The execution is looping: the last state should be
    somewhere else in the sequence. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    # First parse `spec` and return None if this fails.
    parsed = parse_react(spec)
    if parsed is None:
        return None
    # Retrieve the model from the global database.
    model = pynusmv.glob.prop_database().master.bddFsm
    # Handle the terms of the conjunctions separately.
    # If any of them is not satisfied then the whole conjunction is unsatisfied.
    for lhs, rhs in parsed:
        # We need to check whether `model` satisfies GF lhs -> GF rhs.
        # Check GF rhs first since the counterexample is found when checking GF lhs,
        # and that's expensive.

        # If GF rhs is satisfied then the whole implication is satisfied.
        if not repeatedly(model, rhs):
            # If GF rhs is not satisfied then we need to check whether GF lhs is
            # satisfied. If it is then the given trace is a counterexample
            # for the whole GF lhs -> GF rhs.
            res, trace = repeatedly_explain(model, lhs)
            if res:
                return False, trace

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    type_ltl = pynusmv.prop.propTypes['LTL']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        print(spec)
        if prop.type != type_ltl:
            print("property is not LTLSPEC, skipping")
            continue
        res = check_explain_react_spec(spec)
        if res == None:
            print('Property is not a Reactivity formula, skipping')
        elif res[0] == True:
            print("Property is respected")
        elif res[0] == False:
            print("Property is not respected")
            print("Counterexample:", res[1])

    pynusmv.init.deinit_nusmv()
