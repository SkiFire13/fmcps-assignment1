from collections import deque

import pynusmv
import sys

pynusmv.init.init_nusmv()
# BDD_TRUE =  pynusmv.dd.BDD.true()
# BDD_FALSE =  pynusmv.dd.BDD.false()
INV_TYPE = pynusmv.prop.propTypes['Invariant']

def spec_to_bdd(model, spec):
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def reachable(model, spec):
    bddspec = spec_to_bdd(model, spec)
    reach = model.init
    new = model.init
    while new.isnot_false():
        conj = new & bddspec
        if conj.isnot_false(): 
            return True
        new = model.post(new) - reach
        reach = reach | new
    return False

def build_trace(model, frontiers, last):
    # print(len(frontiers), "elements in frontier")
    # print("last state:", last.get_str_values())
    if not frontiers:
        return [last.get_str_values()]
    front = frontiers.pop()
    pred = model.pre(last)
    state = model.pick_one_state(front & pred)
    inputs = model.get_inputs_between_states(state, last)
    input = model.pick_one_inputs(inputs)
    trace = build_trace(model, frontiers, state)
    trace.append(input.get_str_values())
    trace.append(last.get_str_values())
    return trace

def explain_reachable(model, spec):
    bddspec = spec_to_bdd(model, spec)
    reach = model.init
    new = model.init
    frontiers = pynusmv.dd.BDDList()
    while new.isnot_false():
        conj = new & bddspec
        if conj.isnot_false():
            # print("Property reached, building trace")            
            last = model.pick_one_state(conj)
            trace = build_trace(model, frontiers, last)
            return (True, trace)
        frontiers.append(new)
        new = model.post(new) - reach
        reach = reach | new
    return (False, [])
    


    
def unreachable(model, spec):
    negspec = pynusmv.prop.not_(spec)
    # print(negspec)
    res = reachable(model, negspec)
    return not res

def explain_unreachable(model, spec):
    negspec = pynusmv.prop.not_(spec)
    # print(negspec)
    res, trace = explain_reachable(model, negspec)
    # print("Reachablity:", res, trace)
    return (not res, trace)

if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
model = pynusmv.glob.prop_database().master.bddFsm
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    if prop.type == INV_TYPE:
        print("Property", spec, "is an invariant.")
        # print(prop.bddFsm.init)
        res, trace = explain_unreachable(model, spec)
        if res == True:
            print("property is respected")
        else:
            print("property is not respected")
            print(trace)

    else:
        print("Property", spec, "is not an invariant, skipped.")

pynusmv.init.deinit_nusmv()
