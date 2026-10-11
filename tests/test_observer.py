"""CNOT, traccia parziale, purezza nel punto razionale."""

from fractions import Fraction

import pytest

from universe.epistemology import born, norm_squared
from universe.observer import (
    cnot,
    cnot01,
    cnot02,
    cnot12,
    determinant_2x2,
    no_signalling_gap,
    no_signalling_three,
    purity,
    reduced,
)
from universe.ontology import Operator, State, tensor_index_assoc, tensor_state
from universe.ring import Poly, Ring, g
from universe.worlds.qubit import QubitUniverse


def _amp(ring: Ring, real: str, imag: str) -> Poly:
    return ring.var(real) + ring.var(imag) * ring.constant(g(0, 1))


def test_cnot_squares_to_identity():
    ring = Ring(())
    gate = cnot(ring)
    eye = Operator.eye(ring, 4)
    square = gate.matmul(gate)
    assert square.rows == eye.rows


def test_cnot_swaps_ten_and_eleven():
    ring = Ring(())
    one, zero = ring.one(), ring.zero()
    ket10 = State((zero, zero, one, zero))
    ket11 = State((zero, zero, zero, one))
    gate = cnot(ring)
    assert gate.apply(ket10).amplitudes == ket11.amplitudes
    assert gate.apply(ket11).amplitudes == ket10.amplitudes
    assert gate.apply(gate.apply(ket10)).amplitudes == ket10.amplitudes


def test_cnot_preserves_norm_of_generic_state():
    ring = Ring(("a0r", "a0i", "a1r", "a1i", "a2r", "a2i", "a3r", "a3i"))
    state = State(tuple(_amp(ring, f"a{k}r", f"a{k}i") for k in range(4)))
    image = cnot(ring).apply(state)
    assert norm_squared(image) == norm_squared(state)


def test_product_has_zero_determinant():
    ring = Ring(("p0r", "p0i", "p1r", "p1i", "q0r", "q0i", "q1r", "q1i"))
    psi = State((_amp(ring, "p0r", "p0i"), _amp(ring, "p1r", "p1i")))
    phi = State((_amp(ring, "q0r", "q0i"), _amp(ring, "q1r", "q1i")))
    assert determinant_2x2(tensor_state(psi, phi)).is_zero()


def test_determinant_rejects_other_dimensions():
    ring = Ring(())
    with pytest.raises(ValueError, match="quattro ampiezze"):
        determinant_2x2(State((ring.one(), ring.zero())))


def test_rational_point_is_not_a_product():
    world = QubitUniverse()
    point = {
        "c": g(Fraction(3, 5)),
        "s": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    coupled = cnot(world.scalars.ring).apply(
        tensor_state(world.evolve(world.ground()), world.ground())
    )
    det = determinant_2x2(coupled).evaluate(point)
    assert det == g(0, Fraction(-12, 25))
    assert g(Fraction(3, 5)) * g(0, Fraction(-4, 5)) == det


def test_reduced_rejects_a_state_of_the_wrong_dimension():
    ring = Ring(())
    state = State((ring.one(), ring.zero()))
    with pytest.raises(ValueError, match="lo stato non ha la dimensione del composto"):
        reduced(state, 0, 2, 2)


def test_reduced_rejects_an_unknown_factor():
    ring = Ring(())
    one, zero = ring.one(), ring.zero()
    state = State((one, zero, zero, zero))
    with pytest.raises(ValueError, match="fattore sconosciuto"):
        reduced(state, 2, 2, 2)


def test_decoherence_on_a_fresh_ring():
    ring = Ring(("p0r", "p0i", "p1r", "p1i"))
    imag = ring.constant(g(0, 1))
    alpha = ring.var("p0r") + ring.var("p0i") * imag
    beta = ring.var("p1r") + ring.var("p1i") * imag
    psi = State((alpha, beta))
    ket = State((ring.one(), ring.zero()))
    before = reduced(tensor_state(psi, ket), 0, 2, 2)
    assert before.rows[0][1] == alpha * beta.conj()
    after = reduced(cnot(ring).apply(tensor_state(psi, ket)), 0, 2, 2)
    weights = tuple(amplitude.modulus_squared() for amplitude in psi.amplitudes)
    assert after.rows[0][1].is_zero()
    assert after.rows[1][0].is_zero()
    assert after.rows[0][0] == weights[0]
    assert after.rows[1][1] == weights[1]


def test_point_purity_is_mixed():
    world = QubitUniverse()
    point = {
        "c": g(Fraction(3, 5)),
        "s": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    coupled = cnot(world.scalars.ring).apply(
        tensor_state(world.evolve(world.ground()), world.ground())
    )
    value = purity(reduced(coupled, 0, 2, 2)).evaluate(point)
    assert value == g(Fraction(337, 625))
    assert Fraction(337, 625) < 1


def test_three_qubit_cnots_swap_the_named_cells():
    ring = Ring(())
    one, zero = ring.one(), ring.zero()
    basis = []
    for index in range(8):
        amplitudes = [zero] * 8
        amplitudes[index] = one
        basis.append(State(tuple(amplitudes)))
    first, second, friend = cnot01(ring), cnot02(ring), cnot12(ring)
    eye = Operator.eye(ring, 8)
    assert first.matmul(first).rows == eye.rows
    assert second.matmul(second).rows == eye.rows
    assert friend.matmul(friend).rows == eye.rows
    assert first.apply(basis[4]).amplitudes == basis[6].amplitudes
    assert first.apply(basis[5]).amplitudes == basis[7].amplitudes
    assert first.apply(basis[6]).amplitudes == basis[4].amplitudes
    assert first.apply(basis[7]).amplitudes == basis[5].amplitudes
    assert second.apply(basis[4]).amplitudes == basis[5].amplitudes
    assert second.apply(basis[5]).amplitudes == basis[4].amplitudes
    assert second.apply(basis[6]).amplitudes == basis[7].amplitudes
    assert second.apply(basis[7]).amplitudes == basis[6].amplitudes
    assert friend.apply(basis[2]).amplitudes == basis[3].amplitudes
    assert friend.apply(basis[3]).amplitudes == basis[2].amplitudes
    assert friend.apply(basis[6]).amplitudes == basis[7].amplitudes
    assert friend.apply(basis[7]).amplitudes == basis[6].amplitudes


def test_two_observers_agree_on_a_fresh_ring():
    ring = Ring(("p0r", "p0i", "p1r", "p1i"))
    imag = ring.constant(g(0, 1))
    alpha = ring.var("p0r") + ring.var("p0i") * imag
    beta = ring.var("p1r") + ring.var("p1i") * imag
    psi = State((alpha, beta))
    ket = State((ring.one(), ring.zero()))
    zero = ring.zero()
    prepared = tensor_state(tensor_state(psi, ket), ket)
    prepared_right = tensor_state(psi, tensor_state(ket, ket))
    first, second = cnot01(ring), cnot02(ring)
    expected = (alpha, zero, zero, zero, zero, zero, zero, beta)
    ghz = second.apply(first.apply(prepared))
    assert ghz.amplitudes == expected
    assert first.apply(second.apply(prepared)).amplitudes == expected
    assert second.apply(first.apply(prepared_right)).amplitudes == expected
    assert first.apply(second.apply(prepared_right)).amplitudes == expected
    weights = born(ghz)
    assert weights[0] == alpha.modulus_squared()
    assert weights[7] == beta.modulus_squared()
    assert all(weight.is_zero() for weight in weights[1:7])


def test_wigner_reads_the_friend_on_a_fresh_ring():
    ring = Ring(("p0r", "p0i", "p1r", "p1i"))
    imag = ring.constant(g(0, 1))
    alpha = ring.var("p0r") + ring.var("p0i") * imag
    beta = ring.var("p1r") + ring.var("p1i") * imag
    psi = State((alpha, beta))
    ket = State((ring.one(), ring.zero()))
    zero = ring.zero()
    prepared = tensor_state(tensor_state(psi, ket), ket)
    friend, wigner, fanout = cnot01(ring), cnot12(ring), cnot02(ring)
    expected = (alpha, zero, zero, zero, zero, zero, zero, beta)
    chain = wigner.apply(friend.apply(prepared))
    assert chain.amplitudes == expected
    assert chain.amplitudes == fanout.apply(friend.apply(prepared)).amplitudes
    assert wigner.matmul(wigner).rows == Operator.eye(ring, 8).rows
    weights = born(chain)
    assert weights[0] == alpha.modulus_squared()
    assert weights[7] == beta.modulus_squared()
    assert all(weight.is_zero() for weight in weights[1:7])


def test_undoing_the_friend_until_the_record_is_copied():
    ring = Ring(("p0r", "p0i", "p1r", "p1i"))
    imag = ring.constant(g(0, 1))
    alpha = ring.var("p0r") + ring.var("p0i") * imag
    beta = ring.var("p1r") + ring.var("p1i") * imag
    psi = State((alpha, beta))
    ket = State((ring.one(), ring.zero()))
    zero = ring.zero()
    prepared = tensor_state(tensor_state(psi, ket), ket)
    friend, wigner = cnot01(ring), cnot12(ring)
    restored = friend.apply(friend.apply(prepared))
    assert restored.amplitudes == prepared.amplitudes
    coherence = alpha * beta.conj()
    weights = (alpha.modulus_squared(), beta.modulus_squared())
    prepared_system = reduced(prepared, 0, 2, 4)
    assert prepared_system.rows[0][0] == weights[0]
    assert prepared_system.rows[1][1] == weights[1]
    assert prepared_system.rows[0][1] == coherence
    assert prepared_system.rows[1][0] == beta * alpha.conj()
    assert reduced(restored, 0, 2, 4).rows[0][1] == coherence
    undone = friend.apply(wigner.apply(friend.apply(prepared)))
    assert undone.amplitudes == (alpha, zero, zero, zero, zero, beta, zero, zero)
    system = reduced(undone, 0, 2, 4)
    assert system.rows[0][1].is_zero()
    assert system.rows[1][0].is_zero()
    assert system.rows[0][0] == weights[0]
    assert system.rows[1][1] == weights[1]
    record = reduced(undone, 1, 4, 2)
    assert record.rows[0][0] == weights[0]
    assert record.rows[1][1] == weights[1]


def test_rational_point_of_wigners_friend():
    world = QubitUniverse()
    point = {
        "c": g(Fraction(3, 5)),
        "s": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    ring = world.scalars.ring
    ket = world.ground()
    lab = tensor_state(tensor_state(world.evolve(ket), ket), ket)
    friend, wigner = cnot01(ring), cnot12(ring)
    undone = reduced(friend.apply(friend.apply(lab)), 0, 2, 4)
    assert undone.rows[0][1].evaluate(point) == g(0, Fraction(12, 25))
    assert purity(undone).evaluate(point) == g(1)
    copied_state = friend.apply(wigner.apply(friend.apply(lab)))
    copied = reduced(copied_state, 0, 2, 4)
    assert copied.rows[0][1].evaluate(point) == g(0)
    assert copied.rows[1][0].evaluate(point) == g(0)
    assert purity(copied).evaluate(point) == g(Fraction(337, 625))
    record = reduced(copied_state, 1, 4, 2)
    assert record.rows[0][0].evaluate(point) == g(Fraction(9, 25))
    assert record.rows[1][1].evaluate(point) == g(Fraction(16, 25))


def test_local_unitary_on_a_generic_state_does_not_signal():
    gap0, gap1 = no_signalling_gap()
    assert gap0.certification() is None
    assert gap1.certification() is None


def test_local_unitary_on_three_qubits_does_not_signal():
    wigner0, wigner1, friend0, friend1 = no_signalling_three()
    assert wigner0.certification() is None
    assert wigner1.certification() is None
    assert friend0.certification() is None
    assert friend1.certification() is None


def test_tensor_index_assoc():
    assert all(
        tensor_index_assoc(i, j, k, nb, nc)
        for nb in range(1, 4)
        for nc in range(1, 4)
        for i in range(3)
        for j in range(nb)
        for k in range(nc)
    )
