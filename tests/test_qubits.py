import pytest

from universe.dynamics import evolution, hamiltonian
from universe.epistemology import born, marginal, norm_squared
from universe.observer import cnot, cnot01, cnot02, reduced
from universe.ontology import Operator, State
from universe.qubits import (
    cnot_from_0,
    embed_qubit,
    fanout,
    generic_state,
    marginal_at,
    on_qubit,
    reduce_at,
)
from universe.ring import Ring, g


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


def test_reduce_at_matches_the_bipartition():
    _, pair = generic_state(2)
    assert reduce_at(pair, 0).rows == reduced(pair, 0, 2, 2).rows
    assert reduce_at(pair, 1).rows == reduced(pair, 1, 2, 2).rows
    _, triple = generic_state(3)
    assert reduce_at(triple, 0).rows == reduced(triple, 0, 2, 4).rows
    assert reduce_at(triple, 2).rows == reduced(triple, 1, 4, 2).rows


def test_reduce_at_diagonal_is_the_marginal():
    _, triple = generic_state(3)
    rho = reduce_at(triple, 1)
    p0, p1 = marginal_at(triple, 1)
    assert rho.rows[0][0] == p0
    assert rho.rows[1][1] == p1


def test_reduce_at_rejects_a_missing_qubit():
    _, state = generic_state(2)
    with pytest.raises(ValueError):
        reduce_at(state, 2)


def test_embed_qubit_puts_psi_on_the_chosen_bit():
    law, psi = generic_state(1)
    imag = law.ring.constant(g(0, 1))
    rest = (
        law.ring.var("a0r") + law.ring.var("a0i") * imag,
        law.ring.var("a1r") + law.ring.var("a1i") * imag,
    )
    high = embed_qubit(psi, rest, 0)
    assert high.amplitudes[0] == psi.amplitudes[0] * rest[0]
    assert high.amplitudes[1] == psi.amplitudes[0] * rest[1]
    assert high.amplitudes[2] == psi.amplitudes[1] * rest[0]
    low = embed_qubit(psi, rest, 1)
    assert low.amplitudes[0] == psi.amplitudes[0] * rest[0]
    assert low.amplitudes[1] == psi.amplitudes[1] * rest[0]
    assert low.amplitudes[2] == psi.amplitudes[0] * rest[1]


def test_product_reduced_state_is_the_scaled_projector():
    law, psi = generic_state(1, ("b0r", "b0i", "b1r", "b1i"))
    imag = law.ring.constant(g(0, 1))
    rest = tuple(
        law.ring.var(f"b{k}r") + law.ring.var(f"b{k}i") * imag for k in range(2)
    )
    weight = norm_squared(State(rest))
    alpha, beta = psi.amplitudes
    pure = Operator.from_rows(
        [
            [alpha.modulus_squared(), alpha * beta.conj()],
            [beta * alpha.conj(), beta.modulus_squared()],
        ]
    ).scale(weight)
    for qubit in range(2):
        rho = reduce_at(embed_qubit(psi, rest, qubit), qubit)
        assert rho.rows == pure.rows


def test_gates_on_different_qubits_commute():
    law, state = generic_state(
        2,
        tuple(
            f"{prefix}{row}{col}{part}"
            for prefix in ("u", "v")
            for row in range(2)
            for col in range(2)
            for part in ("r", "i")
        ),
    )
    imag = law.ring.constant(g(0, 1))

    def gate(prefix: str) -> Operator:
        rows = []
        for row in range(2):
            rows.append(
                [
                    law.ring.var(f"{prefix}{row}{col}r")
                    + law.ring.var(f"{prefix}{row}{col}i") * imag
                    for col in range(2)
                ]
            )
        return Operator.from_rows(rows)

    left, right = gate("u"), gate("v")
    forward = on_qubit(left, 0, 2).apply(on_qubit(right, 1, 2).apply(state))
    backward = on_qubit(right, 1, 2).apply(on_qubit(left, 0, 2).apply(state))
    assert forward.amplitudes == backward.amplitudes


def test_cnot_from_0_matches_the_observer_gates():
    ring = Ring(())
    assert cnot_from_0(2, 0, ring).rows == Operator.eye(ring, 4).rows
    assert cnot_from_0(2, 1, ring).rows == cnot(ring).rows
    assert cnot_from_0(3, 1, ring).rows == cnot01(ring).rows
    assert cnot_from_0(3, 2, ring).rows == cnot02(ring).rows


def test_cnot_from_0_rejects_a_missing_qubit():
    ring = Ring(())
    with pytest.raises(ValueError):
        cnot_from_0(2, 2, ring)


def test_fanout_is_ghz_and_the_system_is_diagonal():
    _, psi = generic_state(1)
    alpha, beta = psi.amplitudes
    weights = born(psi)
    for n in range(1, 5):
        state = fanout(psi, n)
        assert state.amplitudes[0] == alpha
        assert state.amplitudes[-1] == beta
        assert all(amplitude.is_zero() for amplitude in state.amplitudes[1:-1])
    copied = fanout(psi, 3)
    for left in range(3):
        for right in range(left + 1, 3):
            for index, amplitude in enumerate(copied.amplitudes):
                bit_left = (index >> (2 - left)) & 1
                bit_right = (index >> (2 - right)) & 1
                if bit_left != bit_right:
                    assert amplitude.modulus_squared().is_zero()
    rho = reduce_at(copied, 0)
    assert rho.rows[0][1].is_zero()
    assert rho.rows[1][0].is_zero()
    assert rho.rows[0][0] == weights[0]
    assert rho.rows[1][1] == weights[1]


def test_fanout_rejects_a_state_that_is_not_one_qubit():
    _, state = generic_state(2)
    with pytest.raises(ValueError):
        fanout(state, 3)
