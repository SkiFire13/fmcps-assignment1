import pynusmv
import sys

from collections import deque

from typing import Literal, Optional, Tuple, Union

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
    working: deque[Spec] = deque()
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

def find_looping_state(model: BddFsm, recur: BDD, prereach: BDD) -> Tuple[State, list[BDD]]:
    """
    Returns state and set of frontiers such that:
    - the state is in recur;
    - all the states in the frontiers are in prereach;
    - the frontiers start from the returned state (excluded);
    - the frontiers end in a set of states including the returned one.
    """
    # Start by picking one state
    s = model.pick_one_state(recur)
    r = BDD.false()
    while True:
        # Compute the states in prereach reachable by s in at least one step.
        new = model.post(s) & prereach
        loop_frontiers = []
        # As long as we can reach new states...
        while new.isnot_false():
            loop_frontiers.append(new)
            # We found s, so it is a looping state.
            if s.entailed(new):
                return s, loop_frontiers
            # Otherwise compute the new iteration.
            r = r + new
            new = (model.post(new) & prereach) - r
        # s can't reach itself, so try again with the states in recur that s reached.
        r = r & recur
        s = model.pick_one_state(r)

def build_counterexample_trace(model: BddFsm, recur: BDD, prereach: BDD, frontiers: list[BDD]) -> list[State]:
    """
    Build a counterexample trace, that is an execution that reaches a state in recur and then reaches
    the same state again by only visiting states in prereach.
    """
    # Find the looping state and the set of frontiers in the loop
    s, loop_frontiers = find_looping_state(model, recur, prereach)

    # Build the trace backwards, so the last state is the looping one.
    trace = [s]

    # The last frontier is the one including the looping state, ignore it.
    loop_frontiers.pop()
    # Visit the loop_frontiers backwards, each time finding a state in the
    # frontier that leads to the last state in the trace.
    for frontier in reversed(loop_frontiers):
        trace.append(model.pick_one_state(model.pre(trace[-1]) & frontier))

    # Ignore all the reach frontiers after the one that reached s.
    while not s.entailed(frontiers[-1]):
        frontiers.pop()
    # Same as before, but with the reach frontiers.
    for frontier in reversed(frontiers):
        trace.append(model.pick_one_state(model.pre(trace[-1]) & frontier))

    # Reverse the trace since we built it backward.
    return list(reversed(trace))

def trace_to_explanation(model: BddFsm, trace: list[State]) -> list[dict[str, str]]:
    """
    Create a textual explanation of a given trace, that is a list of
    alternating (textual) states and inputs that match the given symbolic states.
    """
    # Start with the initial state.
    explanation = [trace[0].get_str_values()]
    # For each consecutive pair of states:
    for s1, s2 in zip(trace, trace[1:]):
        # Pick one input between the states.
        inputs = model.get_inputs_between_states(s1, s2)
        input = model.pick_one_inputs(inputs)
        # Add their textual representation to the list.
        explanation.append(input.get_str_values())
        explanation.append(s2.get_str_values())
    return explanation

Res = Union[Tuple[Literal[True], None], Tuple[Literal[False], list[dict[str, str]]]]

def check_explain_react_single(model: BddFsm, reach: BDD, frontiers: list[BDD], lhs: Spec, rhs: Spec) -> Res:
    """
    Returns whether `model` satisfies or not the reactivity formula `GF lhs -> GF rhs`,
    that is, whether all executions of the model satisfy it or not.
    Returns also an explanation for why the model does not satisfy the formula, if it is the case.

    The result is a tuple where the first element is a boolean telling whether the formula is satisfied,
    and the second element is either `None` if the first element is `True`, or an execution
    of the SMV model violating `spec` otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ending with a state. The execution is looping: the last state should be
    somewhere else in the sequence. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.

    `reach` must be the set of reachable states of `model` and `reach_frontiers` must be
    the list of frontiers explored while looking for it.
    """

    # Convert the boolean formulas to BDDs.
    bddlhs = spec_to_bdd(model, lhs)
    bddrhs = spec_to_bdd(model, rhs)

    # Candidate for the set of states we're looking for.
    recur = (reach & bddlhs) - bddrhs

    # While there are possible candidates...
    while recur.isnot_false():
        # Consider the states that can reach recur but don't satisfy g
        new = model.pre(recur) - bddrhs
        prereach = BDD.false()

        # While there are new states to visit...
        while new.isnot_false():
            prereach = prereach + new

            # We reached recur, so there must be a loop between its states.
            if recur.entailed(prereach):
                # Build the counterexample trace and convert it to a textual explanation.
                trace = build_counterexample_trace(model, recur, prereach, frontiers)
                return False, trace_to_explanation(model, trace)

            # Compute the next frontier.
            new = (model.pre(new) - bddrhs) - prereach

        # Update the candidate set.
        recur = recur & prereach

    return True, None

def check_explain_react_spec(spec: Spec) -> Optional[Res]:
    """
    Returns whether the loaded SMV model satisfies or not the reactivity formula
    `spec`, that is, whether all executions of the model satisfy `spec`
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

    # Compute the set of reachable states.
    reach = model.init
    new = model.init
    reach_frontiers = []
    while new.isnot_false():
        reach_frontiers.append(new)
        new = model.post(new) - reach
        reach = reach + new

    # For each subformula check if it holds. If it doesn't return False.
    for lhs, rhs in parsed:
        res = check_explain_react_single(model, reach, reach_frontiers, lhs, rhs)
        if not res[0]:
            return False, res[1]
    return True, None

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
        if res is None:
            print('Property is not a Reactivity formula, skipping')
        elif res[0] == True:
            print("Property is respected")
        elif res[0] == False:
            print("Property is not respected")
            print("Counterexample:", res[1])

    pynusmv.init.deinit_nusmv()
