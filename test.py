import pynusmv
import os
from react_mc import check_explain_react_spec

directory = os.fsencode("./examples")
    
for file in os.listdir(directory):
    filename = os.fsdecode(file)
    
    with pynusmv.init.init_nusmv():
        pynusmv.glob.load_from_file("examples/" + filename)
        pynusmv.glob.compute_model()
        type_ltl = pynusmv.prop.propTypes['LTL']
        for prop in pynusmv.glob.prop_database():
            spec = prop.expr
            if prop.type != type_ltl:
                continue
            res = check_explain_react_spec(spec)
            if res is None:
                continue
            correctRes = pynusmv.mc.check_explain_ltl_spec(spec)
            if res[0] != correctRes[0]:
                print(f"Property {spec} not checked correctly:")
                if res[0]:
                    print("We claim it holds, but it doesn't due to this trace:")
                else:
                    print("We claim it doesn't hold due to the following trace, but it does due to this trace")
                for line in (res[1] or correctRes[1] or []):
                    print(line)
