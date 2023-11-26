from .dd import BDD, Inputs, State

class BddFsm:
    init: BDD = ...
    def pre(self, states: BDD) -> BDD: ...
    def post(self, states: BDD) -> BDD: ...
    def pick_one_state(self, bdd: BDD) -> State: ...
    def get_inputs_between_states(self, current: State, next: State) -> BDD: ...
    def pick_one_inputs(self, inputs: BDD) -> Inputs: ...
