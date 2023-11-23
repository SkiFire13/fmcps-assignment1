import pynusmv
import sys

from typing import Literal, Optional

from pynusmv.prop import Spec
from pynusmv.fsm import BddFsm
from pynusmv.dd import BDD

pynusmv.init.init_nusmv()

LTL_TYPE = pynusmv.prop.propTypes['LTL']

CONTEXT_TYPE = 130
IMPLIES_TYPE = 164
G_TYPE = 186
F_TYPE = 187

def spec_to_bdd(model, spec):
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

# TODO: Handle &s
def parse_react(spec: Spec) -> Optional[tuple[Spec, Spec]]:
    if spec.type == CONTEXT_TYPE:
        return parse_react(spec.cdr)
    
    if spec.type != IMPLIES_TYPE:
        return None
    
    def parse_gf(spec: Spec):
        if spec.type != G_TYPE or spec.car.type != F_TYPE:
            return None
        return spec.car.car

    lhs = parse_gf(spec.car)
    rhs = parse_gf(spec.cdr)

    if lhs is None or rhs is None:
        return None
    
    return lhs, rhs

def reachable_bdd(model: BddFsm) -> BDD:
    reach = model.init
    new = model.init
    while new.isnot_false():
        new = model.post(new) - reach
        reach = reach + new
    return reach

def repeatedly(model: BddFsm, spec: Spec) -> bool:
    bddspec = spec_to_bdd(model, spec)
    recur = reachable_bdd(model) & bddspec
    while recur.isnot_false():
        prereach = BDD.false()
        new = model.pre(recur)
        while new.isnot_false():
            prereach = prereach + new
            if prereach.imply(recur):
                return True
            new = model.pre(new) - prereach
        recur = recur & prereach
    return False

def trace_until(model: BddFsm, start: BDD, goal: BDD) -> list[BDD]:
    reach = start
    new = start
    frontiers = []
    while new.isnot_false():
        conj = new & goal
        if conj.isnot_false():
            last = model.pick_one_state(conj)
            return build_trace(model, frontiers, last)
        frontiers.append(new)
        new = model.post(new) - reach
        reach = reach | new
    raise "Trace goal should be reachable"

def build_trace(model: BddFsm, frontiers: list[BDD], last: BDD) -> list[BDD]:
    trace = [last]
    for front in reversed(frontiers):
        pred = model.pre(last)
        state = model.pick_one_state(front & pred)
        trace.append(state)
        last = state
    trace.reverse()
    return trace

def repeatedly_explain(model: BddFsm, spec: Spec) -> tuple[Literal[True], list[BDD]] | tuple[Literal[False], None]:
    bddspec = spec_to_bdd(model, spec)
    recur = reachable_bdd(model) & bddspec
    while recur.isnot_false():
        prereach = BDD.false()
        new = model.pre(recur)
        while new.isnot_false():
            prereach = prereach + new
            if recur.entailed(prereach):
                s = model.pick_one_state(recur)
                reach_trace = trace_until(model, model.init, s)
                reach_loop = trace_until(model, model.post(s), s)
                return True, reach_trace + reach_loop
            new = model.pre(new) - prereach
        recur = recur & prereach
    return False, None

def print_trace(model: BddFsm, trace: list[BDD]):
    for s1, s2 in zip(trace, trace[1:]):
        print(s1.get_str_values())
        inputs = model.get_inputs_between_states(s1, s2)
        input = model.pick_one_inputs(inputs)
        print(input.get_str_values())
    print(trace[-1].get_str_values())

if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
model = pynusmv.glob.prop_database().master.bddFsm
for prop in pynusmv.glob.prop_database():
    if prop.type != LTL_TYPE:
        print("Property", prop.expr, "is not an LTL formula, skipped.")
        continue

    parsed = parse_react(prop.expr)
    if parsed is None:
        print("Property", prop.expr, "is not a Reactivity formula")
        continue

    lhs, rhs = parsed

    res, trace = repeatedly_explain(model, lhs)
    if not res or repeatedly(model, rhs):
        print(f"property {prop.expr} is respected")
    else:
        print(f"property {prop.expr} is not respected")
        print_trace(model, trace)

pynusmv.init.deinit_nusmv()