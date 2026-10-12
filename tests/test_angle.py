"""Somme parziali e legge di addizione, su frazioni."""

from fractions import Fraction

from universe.angle import (
    DEGREE,
    SAMPLES,
    addition_scan,
    angle_at_half,
    axis_reading,
    born_scan,
    c_term,
    circle_at_one,
    circle_gap,
    circle_scan,
    cos_cell,
    cos_coeff,
    cos_conv,
    cos_product,
    cos_sum,
    exp_tail,
    exp_term,
    group_gap_cos,
    group_gap_sin,
    group_remainder,
    group_scan,
    high_band,
    remainder,
    remainder_small_scan,
    s_term,
    sin_cell,
    sin_coeff,
    sin_conv,
    sin_product,
    sin_sum,
    tail_sum,
)
from universe.ring import g


def test_coefficients_have_period_four():
    assert [cos_coeff(k) for k in range(8)] == [1, 0, -1, 0, 1, 0, -1, 0]
    assert [sin_coeff(k) for k in range(8)] == [0, 1, 0, -1, 0, 1, 0, -1]
    for k in range(8):
        assert cos_coeff(k + 1) == -sin_coeff(k)
        assert sin_coeff(k + 1) == cos_coeff(k)


def test_sums_match_terms():
    for x in SAMPLES:
        assert c_term(0, x) == 1
        assert s_term(0, x) == 0
        for n in range(DEGREE + 1):
            assert cos_sum(n, x) == sum(
                (c_term(k, x) for k in range(n + 1)), Fraction(0)
            )
            assert sin_sum(n, x) == sum(
                (s_term(k, x) for k in range(n + 1)), Fraction(0)
            )


def test_discrete_derivative():
    for x in SAMPLES:
        for m in range(DEGREE + 1):
            assert (m + 1) * c_term(m + 1, x) == -x * s_term(m, x)
            assert (m + 1) * s_term(m + 1, x) == x * c_term(m, x)
        for m in range(1, DEGREE + 1):
            assert m * c_term(m, x) == -x * s_term(m - 1, x)
            assert m * s_term(m, x) == x * c_term(m - 1, x)


def test_addition_law():
    for m in range(DEGREE + 1):
        for x in SAMPLES:
            for y in SAMPLES:
                cosine = sum(
                    (
                        c_term(k, x) * c_term(m - k, y)
                        - s_term(k, x) * s_term(m - k, y)
                        for k in range(m + 1)
                    ),
                    Fraction(0),
                )
                sine = sum(
                    (
                        s_term(k, x) * c_term(m - k, y)
                        + c_term(k, x) * s_term(m - k, y)
                        for k in range(m + 1)
                    ),
                    Fraction(0),
                )
                assert cosine == c_term(m, x + y)
                assert sine == s_term(m, x + y)
                assert cos_conv(m, x, y) == cosine
                assert sin_conv(m, x, y) == sine
    holds, _detail = addition_scan()
    assert holds


def test_partial_sums_at_one():
    assert cos_sum(8, Fraction(1)) == Fraction(4357, 8064)
    assert sin_sum(8, Fraction(1)) == Fraction(4241, 5040)


def test_exp_add():
    for m in range(DEGREE + 1):
        for x in SAMPLES:
            for y in SAMPLES:
                total = sum(
                    (exp_term(k, x) * exp_term(m - k, y) for k in range(m + 1)),
                    Fraction(0),
                )
                assert total == exp_term(m, x + y)


def test_circle_identity_and_bound():
    for order in range(DEGREE + 1):
        for sample in SAMPLES:
            gap = circle_gap(order, sample)
            assert gap == tail_sum(order, sample)
            assert abs(gap) <= remainder(order, sample)
    holds, _detail = circle_scan()
    assert holds


def test_circle_at_one():
    cosine, sine, gap, bound = circle_at_one()
    assert cosine == Fraction(4357, 8064)
    assert sine == Fraction(4241, 5040)
    assert gap == Fraction(-6991, 1625702400)
    assert bound == Fraction(373426, 212837625)
    assert abs(gap) <= bound


def test_group_law_and_bound():
    witness = Fraction(1, 2)
    cosine = group_gap_cos(4, witness, witness)
    sine = group_gap_sin(4, witness, witness)
    bound = group_remainder(4, witness, witness)
    assert cosine == Fraction(53, 49152)
    assert sine == Fraction(-71, 9216)
    assert bound == Fraction(401, 40320)
    assert cosine == -high_band(4, witness, witness, cos_cell)
    assert sine == -high_band(4, witness, witness, sin_cell)
    total = witness + witness
    assert cos_product(4, witness, witness) - cos_sum(4, total) == -cosine
    assert sin_product(4, witness, witness) - sin_sum(4, total) == -sine
    assert abs(cosine) <= bound
    assert abs(sine) <= bound
    holds, _detail = group_scan()
    assert holds


def test_born_weights_on_axis():
    witness = Fraction(1, 2)
    cosine, sine, weight0, weight1, gap, bound = angle_at_half()
    assert cosine == cos_sum(4, witness) == Fraction(337, 384)
    assert sine == sin_sum(4, witness) == Fraction(23, 48)
    assert weight0 == Fraction(113569, 147456)
    assert weight1 == Fraction(529, 2304)
    assert gap == Fraction(-31, 147456)
    assert bound == Fraction(401, 40320)
    assert abs(gap) <= bound
    amplitude0, amplitude1, born0, born1 = axis_reading(cosine, sine)
    assert amplitude0 == g(cosine)
    assert amplitude1 == g(0, -sine)
    assert born0 == g(weight0)
    assert born1 == g(weight1)
    holds, _detail = born_scan()
    assert holds


def test_remainder_halves():
    witness = Fraction(1, 2)
    assert 2 * abs(witness) <= Fraction(6, 2)
    rest = remainder(4, witness)
    cap = 2 * exp_term(5, 2 * abs(witness))
    assert rest == exp_tail(4, Fraction(1))
    assert rest == Fraction(401, 40320)
    assert cap == Fraction(1, 60)
    assert rest <= cap
    holds, _detail = remainder_small_scan()
    assert holds
