"""Unit tests for the exact scalars: Gauss arithmetic and the quotient reducer."""

from fractions import Fraction

import pytest

from universe.ring import Ring, g, qubit_scalars, reduce_witness, witness_holds


def test_gauss_arithmetic():
    i = g(0, 1)
    assert i * i == g(-1)
    assert (g(1, 1) * g(1, -1)) == g(2)
    assert g(3, 4).conj() == g(3, -4)
    assert g(Fraction(1, 2), 1) - g(Fraction(1, 2), 1) == g(0)


def test_gauss_pow():
    i = g(0, 1)
    assert i**0 == g(1)
    assert i**4 == g(1)
    assert i**7 == g(0, -1)
    assert g(Fraction(3, 5)) ** 2 == g(Fraction(9, 25))
    with pytest.raises(ValueError):
        i**-1


def test_ring_rejects_duplicates_and_self_reference():
    with pytest.raises(ValueError):
        Ring(("x", "x"))
    ring = Ring(("x", "y"))
    with pytest.raises(ValueError):
        ring.set_square("x", ring.var("x") + ring.one())


def test_circle_reduces_to_zero():
    s = qubit_scalars()
    assert (s.c**2 + s.s**2 - s.one).is_zero()
    assert (s.nx**2 + s.ny**2 + s.nz**2 - s.one).is_zero()


def test_high_powers_peel_completely():
    s = qubit_scalars()
    c_idx = s.ring.index("c")
    p = s.c**9 * s.nx**7
    assert all(exp[c_idx] < 2 for exp, _ in p.terms)
    assert all(exp[s.ring.index("nx")] < 2 for exp, _ in p.terms)
    # c⁹ = c (1 − s²)⁴ in the quotient.
    assert s.c**9 == s.c * (s.one - s.s**2) ** 4


def test_witness_rebuilds_origin():
    s = qubit_scalars()
    p = (s.c**2 + s.s**2 - s.one) * (s.c * s.nx**3 + s.ny)
    cofactors_ok, remainder_zero = p.witness()
    assert cofactors_ok and remainder_zero
    assert p.certification() is None


def test_certification_reports_nonzero_remainder():
    s = qubit_scalars()
    msg = (s.c * s.s).certification()
    assert msg is not None and msg.startswith("resto")


def test_witness_holds_rejects_wrong_cofactors():
    s = qubit_scalars()
    origin = (s.c**2 - s.one).origin
    remainder, factors = reduce_witness(origin)
    assert witness_holds(origin, remainder, factors)
    bumped = (factors[0] + s.one.origin,) + factors[1:]
    assert not witness_holds(origin, remainder, bumped)
    assert not witness_holds(origin, remainder, factors[:1])


def test_certify_extra_sphere():
    s = qubit_scalars()
    sphere = s.ar**2 + s.ai**2 + s.br**2 + s.bi**2
    replacement = s.one - s.ai**2 - s.br**2 - s.bi**2
    assert (sphere - s.one).certify_extra("ar", replacement) is None
    assert (sphere - s.one).certification() is not None
    with pytest.raises(ValueError):
        s.one.certify_extra("c", s.one)


def test_cofactors_are_not_unique():
    s = qubit_scalars()
    origin = ((s.c**2 + s.s**2 - s.one) * s.nx).origin
    remainder, (f_c, f_n) = reduce_witness(origin)
    assert remainder.is_zero()
    # Syzygy: gN·gC − gC·gN = 0, so shifting by it gives another witness.
    g_c = (s.c**2 + s.s**2 - s.one).origin
    g_n = (s.nx**2 + s.ny**2 + s.nz**2 - s.one).origin
    shifted = (f_c + g_n, f_n - g_c)
    assert not shifted[0].eq(f_c)
    assert witness_holds(origin, remainder, shifted)


def test_substitute_and_evaluate_point():
    s = qubit_scalars()
    point = {"c": g(Fraction(3, 5)), "s": g(Fraction(4, 5))}
    assert (s.c**2 + s.s**2).evaluate(point) == g(1)
    assert (s.c * s.nx).substitute(point) == s.nx * s.ring.constant(point["c"])
    with pytest.raises(ValueError):
        s.nx.evaluate(point)


def test_real_imag_split():
    s = qubit_scalars()
    i = s.ring.constant(g(0, 1))
    z = s.ar + s.ai * i
    assert z.modulus_squared().imag_is_zero()
    assert z.modulus_squared() == s.ar**2 + s.ai**2
