"""CNOT, traccia parziale, purezza nel punto razionale."""

from fractions import Fraction

import pytest

from universe.epistemology import norm_squared
from universe.observer import cnot, determinant_2x2, purity, reduced
from universe.ontology import Operator, State, tensor_state
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
