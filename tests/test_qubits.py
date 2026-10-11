import pytest

from universe.dynamics import evolution, hamiltonian
from universe.ontology import Operator
from universe.qubits import generic_state, on_qubit


def test_generic_state_has_free_amplitudes():
    law, state = generic_state(3)
    assert len(state.amplitudes) == 8
    assert law.ring.variables[:5] == ("c", "s", "nx", "ny", "nz")
    assert len(law.ring.variables) == 5 + 16


def test_on_qubit_is_the_tensor_with_identities():
    law, _ = generic_state(2)
    gate = evolution(law, hamiltonian(law))
    eye = Operator.eye(law.ring, 2)
    assert on_qubit(gate, 0, 2).rows == gate.tensor(eye).rows
    assert on_qubit(gate, 1, 2).rows == eye.tensor(gate).rows


def test_on_qubit_rejects_a_missing_qubit():
    law, _ = generic_state(1)
    with pytest.raises(ValueError):
        on_qubit(Operator.eye(law.ring, 2), 1, 1)
