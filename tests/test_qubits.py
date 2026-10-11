import pytest

from universe.dynamics import evolution, hamiltonian
from universe.epistemology import marginal
from universe.ontology import Operator
from universe.qubits import generic_state, marginal_at, on_qubit


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


def test_marginal_at_is_the_born_pair_of_one_qubit():
    _, pair = generic_state(2)
    assert marginal_at(pair, 0) == marginal(pair, 0, 2, 2)
    assert marginal_at(pair, 1) == marginal(pair, 1, 2, 2)
    _, triple = generic_state(3)
    assert marginal_at(triple, 0) == marginal(triple, 0, 2, 4)
    assert marginal_at(triple, 2) == marginal(triple, 1, 4, 2)
    amplitudes = triple.amplitudes
    p0 = (
        amplitudes[0].modulus_squared()
        + amplitudes[1].modulus_squared()
        + amplitudes[4].modulus_squared()
        + amplitudes[5].modulus_squared()
    )
    p1 = (
        amplitudes[2].modulus_squared()
        + amplitudes[3].modulus_squared()
        + amplitudes[6].modulus_squared()
        + amplitudes[7].modulus_squared()
    )
    assert marginal_at(triple, 1) == (p0, p1)


def test_marginal_at_rejects_a_missing_qubit():
    _, state = generic_state(2)
    with pytest.raises(ValueError):
        marginal_at(state, 2)
