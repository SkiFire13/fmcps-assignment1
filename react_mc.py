import pynusmv
import sys

from typing import Literal, Optional

from pynusmv.dd import BDD
from pynusmv.fsm import BddFsm
from pynusmv.prop import Spec

pynusmv.init.init_nusmv()

LTL_TYPE = pynusmv.prop.propTypes['LTL']

CONTEXT_TYPE = 130
AND_TYPE = 169
IMPLIES_TYPE = 164
G_TYPE = 186
F_TYPE = 187

def spec_to_bdd(model, spec):
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def parse_react(spec: Spec) -> Optional[list[Spec, Spec]]:
    if spec.type == CONTEXT_TYPE:
        spec = spec.cdr
    
    stack = [spec]
    parsed = []
    while len(stack) != 0:
        spec = stack.pop()

        if spec.type == AND_TYPE:
            stack.append(spec.car)
            stack.append(spec.cdr)
            continue

        if spec.type != IMPLIES_TYPE:
            return None
    
        def parse_repeatedly(spec: Spec):
            if spec.type != G_TYPE or spec.car.type != F_TYPE:
                return None
            return spec.car.car

        lhs = parse_repeatedly(spec.car)
        rhs = parse_repeatedly(spec.cdr)

        if lhs is None or rhs is None:
            return None
        
        parsed.append((lhs, rhs))

    return parsed

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
            if recur.entailed(prereach):
                return True
            new = model.pre(new) - prereach
        recur = recur & prereach
    return False

def path_from_frontiers(model: BddFsm, frontiers: list[BDD], last: BDD) -> list[BDD]:
    path = [last]
    for front in reversed(frontiers):
        pred = model.pre(last)
        state = model.pick_one_state(front & pred)
        path.append(state)
        last = state
    path.reverse()
    return path

def find_path(model: BddFsm, start: BDD, goal: BDD) -> list[BDD]:
    reach = start
    new = start
    frontiers = []
    while new.isnot_false():
        conj = new & goal
        if conj.isnot_false():
            last = model.pick_one_state(conj)
            return path_from_frontiers(model, frontiers, last)
        frontiers.append(new)
        new = model.post(new) - reach
        reach = reach + new
    raise "Path doesn't exist"

def path_to_trace(model: BddFsm, path: list[BDD]) -> list[dict[str, str]]:
    trace = [path[0].get_str_values()]
    for s1, s2 in zip(path, path[1:]):
        inputs = model.get_inputs_between_states(s1, s2)
        input = model.pick_one_inputs(inputs)
        trace.append(input.get_str_values())
        trace.append(s2.get_str_values())
    return trace

def find_looping_state(model: BddFsm, recur: BDD) -> BDD:
    while True:
        postreach = BDD.false()
        new = model.post(recur)
        while new.isnot_false():
            postreach = postreach + new
            if recur.entailed(postreach):
                return model.pick_one_state(recur)
            new = model.post(postreach) - postreach
        recur = recur & postreach

def build_trace(model: BddFsm, recur: BDD) -> list[dict[str, str]]:
    s = find_looping_state(model, recur)
    reach_trace = find_path(model, model.init, s)
    loop_trace = find_path(model, model.post(s), s)
    return path_to_trace(model, reach_trace + loop_trace)

def repeatedly_explain(model: BddFsm, spec: Spec) -> tuple[Literal[True], list[BDD]] | tuple[Literal[False], None]:
    bddspec = spec_to_bdd(model, spec)
    recur = reachable_bdd(model) & bddspec
    while recur.isnot_false():
        prereach = BDD.false()
        new = model.pre(recur)
        while new.isnot_false():
            prereach = prereach + new
            if recur.entailed(prereach):
                return True, build_trace(model, recur)
            new = model.pre(new) - prereach
        recur = recur & prereach
    return False, None

def check_explain_react_spec(model: BddFsm, spec: Spec) -> Optional[tuple[Literal[True], None] | tuple[Literal[False], list[BDD]]]:
    parsed = parse_react(spec)
    if parsed is None:
        return None
    for lhs, rhs in parsed:
        res, trace = repeatedly_explain(model, lhs)
        if res and not repeatedly(model, rhs):
            return False, trace
    return True, None

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

    spec = prop.expr
    optres = check_explain_react_spec(model, spec)
    if optres is None:
        print(f"property {prop.expr} is not a valid Reactive formula")
        continue

    res, trace = optres
    if res:
        print(f"property {prop.expr} is respected")
    else:
        print(f"property {prop.expr} is not respected")
        for line in trace:
            print(line)

pynusmv.init.deinit_nusmv()
