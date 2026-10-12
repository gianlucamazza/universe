"""Somme parziali di coseno e seno su un razionale.

`c_term(k, x)` è `cos_coeff(k) · xᵏ / k!`, `s_term` il seno.
`cos_sum` e `sin_sum` sommano fino al grado `n`. Non è un limite.
La convoluzione fino a `m` è il termine in `x + y`:
`Universe.Angle.angle_add_cos`, `Universe.Angle.angle_add_sin`.
`exp_term` è `xᵐ / m!`: la stessa legge è `Universe.Angle.exp_add`.
`C_n² + S_n² − 1` è `tail_sum`, e il valore assoluto sta sotto
`remainder` (`Universe.Angle.circle_tail`, `Universe.Angle.circle_bound`).
Lo scarto della legge di gruppo è la banda alta, e il valore assoluto
sta sotto la coda di `exp(|x| + |y|)` (`Universe.Angle.group_bound_cos`,
`Universe.Angle.group_bound_sin`). Se `2|x| ≤ (N + 2) / 2`, `remainder`
sta sotto il doppio del primo termine (`Universe.Angle.remainder_small`).
In `(c, s) = (C_N(φ), S_N(φ))`, lungo `e_x`, `U|0⟩` ha ampiezze `C_N` e
`−i S_N` e pesi `C_N²`, `S_N²` (`Universe.Angle.angle_born`). La lettura
è sull'anello libero: il quoziente sostituirebbe `c²` con `1 − s²`.
`Universe.Angle.angle_half` è il punto `φ = 1/2`, `N = 4`.
I coefficienti ripetono `Universe.Series.cosCoeff` e
`Universe.Series.sinCoeff`.
"""

from __future__ import annotations

from collections.abc import Callable
from fractions import Fraction
from functools import cache
from math import factorial

from universe.dynamics import evolution, hamiltonian
from universe.epistemology import born
from universe.ontology import State
from universe.ring import Gauss, Poly, g, law_ring

DEGREE = 12

SAMPLES: tuple[Fraction, ...] = (
    Fraction(0),
    Fraction(1),
    Fraction(-1),
    Fraction(1, 2),
    Fraction(3, 5),
    Fraction(-4, 5),
)


def _rat(value: Fraction) -> str:
    if value < 0:
        return f"−{-value}"
    return str(value)


def cos_coeff(n: int) -> int:
    """`1, 0, −1, 0, …` con periodo quattro, come `Universe.Series.cosCoeff`."""
    return (1, 0, -1, 0)[n % 4]


def sin_coeff(n: int) -> int:
    """`0, 1, 0, −1, …` con periodo quattro, come `Universe.Series.sinCoeff`."""
    return (0, 1, 0, -1)[n % 4]


def c_term(k: int, x: Fraction) -> Fraction:
    """Termine `cos_coeff(k) · xᵏ / k!`."""
    return Fraction(cos_coeff(k)) * x**k / factorial(k)


def s_term(k: int, x: Fraction) -> Fraction:
    """Termine `sin_coeff(k) · xᵏ / k!`."""
    return Fraction(sin_coeff(k)) * x**k / factorial(k)


def cos_sum(n: int, x: Fraction) -> Fraction:
    """`C_n(x)`, la somma dei termini di coseno fino a `n`."""
    return sum((c_term(k, x) for k in range(n + 1)), Fraction(0))


def sin_sum(n: int, x: Fraction) -> Fraction:
    """`S_n(x)`, la somma dei termini di seno fino a `n`."""
    return sum((s_term(k, x) for k in range(n + 1)), Fraction(0))


def cos_conv(m: int, x: Fraction, y: Fraction) -> Fraction:
    """`Σ_{k ≤ m} (c_k(x) c_{m−k}(y) − s_k(x) s_{m−k}(y))`."""
    total = Fraction(0)
    for k in range(m + 1):
        total += c_term(k, x) * c_term(m - k, y) - s_term(k, x) * s_term(m - k, y)
    return total


def sin_conv(m: int, x: Fraction, y: Fraction) -> Fraction:
    """`Σ_{k ≤ m} (s_k(x) c_{m−k}(y) + c_k(x) s_{m−k}(y))`."""
    total = Fraction(0)
    for k in range(m + 1):
        total += s_term(k, x) * c_term(m - k, y) + c_term(k, x) * s_term(m - k, y)
    return total


def addition_witness() -> tuple[Fraction, Fraction]:
    """Coseno a grado 2 e seno a grado 3, per `x = 1/2` e `y = 3/5`."""
    left, right = Fraction(1, 2), Fraction(3, 5)
    return cos_conv(2, left, right), sin_conv(3, left, right)


def addition_scan(
    degree: int = DEGREE,
    samples: tuple[Fraction, ...] = SAMPLES,
) -> tuple[bool, str]:
    """Legge di addizione per ogni `m ≤ degree` e ogni coppia di `samples`."""
    for m in range(degree + 1):
        for x in samples:
            for y in samples:
                cosine = cos_conv(m, x, y) == c_term(m, x + y)
                sine = sin_conv(m, x, y) == s_term(m, x + y)
                if not (cosine and sine):
                    return (
                        False,
                        f"fallisce a m = {m}, x = {_rat(x)}, y = {_rat(y)}",
                    )
    listed = ", ".join(_rat(sample) for sample in samples)
    cos_two, sin_three = addition_witness()
    return (
        True,
        f"per ogni m ≤ {degree} e per x, y in {{{listed}}}\n"
        f"testimone x = 1/2, y = 3/5: "
        f"grado 2, cos {_rat(cos_two)}; grado 3, sin {_rat(sin_three)}",
    )


def exp_term(m: int, x: Fraction) -> Fraction:
    """Termine `xᵐ / m!`."""
    return x**m / factorial(m)


def circle_cell(j: int, k: int, x: Fraction, y: Fraction) -> Fraction:
    """`c_j(x) c_k(y) + s_j(x) s_k(y)`, `Universe.Angle.circleTerm` con `y = x`."""
    return c_term(j, x) * c_term(k, y) + s_term(j, x) * s_term(k, y)


def tail_sum(n: int, x: Fraction) -> Fraction:
    """Coda oltre il grado `n`: le diagonali alte di `circle_cell`."""
    return high_band(n, x, x, circle_cell)


def exp_tail(n: int, scale: Fraction) -> Fraction:
    """`Σ_{m = n + 1}^{2n} scaleᵐ / m!`."""
    return sum(
        (exp_term(degree, scale) for degree in range(n + 1, 2 * n + 1)),
        Fraction(0),
    )


def remainder(n: int, x: Fraction) -> Fraction:
    """`r_n(x) = Σ_{m = n + 1}^{2n} (2|x|)ᵐ / m!`."""
    return exp_tail(n, 2 * abs(x))


def group_remainder(n: int, x: Fraction, y: Fraction) -> Fraction:
    """Coda di `exp(|x| + |y|)` da `n + 1` a `2n`."""
    return exp_tail(n, abs(x) + abs(y))


def circle_gap(n: int, x: Fraction) -> Fraction:
    """`C_n(x)² + S_n(x)² − 1`."""
    cosine = cos_sum(n, x)
    sine = sin_sum(n, x)
    return cosine * cosine + sine * sine - 1


def circle_scan(
    degree: int = DEGREE,
    samples: tuple[Fraction, ...] = SAMPLES,
) -> tuple[bool, str]:
    """`C_N² + S_N² − 1 = T_N` e `|scarto| ≤ r_N`, per `N ≤ degree`."""
    for order in range(degree + 1):
        for sample in samples:
            gap = circle_gap(order, sample)
            if gap != tail_sum(order, sample) or abs(gap) > remainder(order, sample):
                return (
                    False,
                    f"fallisce a N = {order}, x = {_rat(sample)}",
                )
    listed = ", ".join(_rat(sample) for sample in samples)
    return (True, f"per ogni N ≤ {degree} e per x in {{{listed}}}")


def circle_at_one() -> tuple[Fraction, Fraction, Fraction, Fraction]:
    """`φ = 1`, `N = 8`: coseno, seno, scarto, resto."""
    point = Fraction(1)
    return (
        cos_sum(8, point),
        sin_sum(8, point),
        circle_gap(8, point),
        remainder(8, point),
    )


def cos_cell(j: int, k: int, x: Fraction, y: Fraction) -> Fraction:
    """`c_j(x) c_k(y) − s_j(x) s_k(y)`."""
    return c_term(j, x) * c_term(k, y) - s_term(j, x) * s_term(k, y)


def sin_cell(j: int, k: int, x: Fraction, y: Fraction) -> Fraction:
    """`s_j(x) c_k(y) + c_j(x) s_k(y)`."""
    return s_term(j, x) * c_term(k, y) + c_term(j, x) * s_term(k, y)


def high_band(
    n: int,
    x: Fraction,
    y: Fraction,
    cell: Callable[[int, int, Fraction, Fraction], Fraction],
) -> Fraction:
    """Diagonali `n < m ≤ 2n`: `k` corre da `m − n` a `n`."""
    total = Fraction(0)
    for degree in range(n + 1, 2 * n + 1):
        for index in range(degree - n, n + 1):
            total += cell(index, degree - index, x, y)
    return total


def cos_product(n: int, x: Fraction, y: Fraction) -> Fraction:
    """`C_n(x) C_n(y) − S_n(x) S_n(y)`."""
    return cos_sum(n, x) * cos_sum(n, y) - sin_sum(n, x) * sin_sum(n, y)


def sin_product(n: int, x: Fraction, y: Fraction) -> Fraction:
    """`S_n(x) C_n(y) + C_n(x) S_n(y)`."""
    return sin_sum(n, x) * cos_sum(n, y) + cos_sum(n, x) * sin_sum(n, y)


def group_gap_cos(n: int, x: Fraction, y: Fraction) -> Fraction:
    """`C_n(x + y) − (C_n(x) C_n(y) − S_n(x) S_n(y))`."""
    return cos_sum(n, x + y) - cos_product(n, x, y)


def group_gap_sin(n: int, x: Fraction, y: Fraction) -> Fraction:
    """`S_n(x + y) − (S_n(x) C_n(y) + C_n(x) S_n(y))`."""
    return sin_sum(n, x + y) - sin_product(n, x, y)


def group_witness() -> tuple[Fraction, Fraction, Fraction]:
    """Scarto coseno, scarto seno e resto a `N = 4`, `x = y = 1/2`."""
    witness = Fraction(1, 2)
    return (
        group_gap_cos(4, witness, witness),
        group_gap_sin(4, witness, witness),
        group_remainder(4, witness, witness),
    )


def group_scan(
    degree: int = DEGREE,
    samples: tuple[Fraction, ...] = SAMPLES,
) -> tuple[bool, str]:
    """Scarto della legge di gruppo uguale alla banda alta, e sotto la coda."""
    for order in range(degree + 1):
        for left in samples:
            for right in samples:
                cosine = group_gap_cos(order, left, right)
                sine = group_gap_sin(order, left, right)
                bound = group_remainder(order, left, right)
                cos_tail = high_band(order, left, right, cos_cell)
                sin_tail = high_band(order, left, right, sin_cell)
                if (
                    cosine != -cos_tail
                    or sine != -sin_tail
                    or abs(cosine) > bound
                    or abs(sine) > bound
                ):
                    return (
                        False,
                        f"fallisce a N = {order}, x = {_rat(left)}, y = {_rat(right)}",
                    )
    cosine, sine, bound = group_witness()
    if (
        cosine != Fraction(53, 49152)
        or sine != Fraction(-71, 9216)
        or bound != Fraction(401, 40320)
    ):
        return (False, "il testimone non torna")
    listed = ", ".join(_rat(sample) for sample in samples)
    return (
        True,
        f"per ogni N ≤ {degree} e per x, y in {{{listed}}}\n"
        f"testimone N = 4, x = y = 1/2: "
        f"scarto cos {_rat(cosine)}, scarto sin {_rat(sine)}, "
        f"resto {_rat(bound)}",
    )


def _within_half(n: int, x: Fraction) -> bool:
    return 2 * abs(x) <= Fraction(n + 2, 2)


def remainder_witness() -> tuple[Fraction, Fraction]:
    """Resto e doppio del primo termine a `N = 4`, `x = 1/2`."""
    witness = Fraction(1, 2)
    return remainder(4, witness), 2 * exp_term(5, 2 * abs(witness))


def remainder_small_scan(
    degree: int = DEGREE,
    samples: tuple[Fraction, ...] = SAMPLES,
) -> tuple[bool, str]:
    """Se `2|x| ≤ (N + 2) / 2`, `r_N(x)` sta sotto il doppio del primo termine."""
    for order in range(degree + 1):
        for sample in samples:
            if not _within_half(order, sample):
                continue
            cap = 2 * exp_term(order + 1, 2 * abs(sample))
            if remainder(order, sample) > cap:
                return (
                    False,
                    f"fallisce a N = {order}, x = {_rat(sample)}",
                )
    witness = Fraction(1, 2)
    rest, cap = remainder_witness()
    if (
        not _within_half(4, witness)
        or rest != Fraction(401, 40320)
        or cap != Fraction(1, 60)
        or rest > cap
    ):
        return (False, "il testimone non torna")
    listed = ", ".join(_rat(sample) for sample in samples)
    return (
        True,
        f"per ogni N ≤ {degree} e per x in {{{listed}}} "
        f"con 2|x| ≤ (N + 2) / 2\n"
        f"testimone N = 4, x = 1/2: 2|x| = {_rat(2 * abs(witness))} "
        f"≤ {_rat(Fraction(6, 2))}, resto {_rat(rest)} ≤ {_rat(cap)}",
    )


@cache
def _axis_columns() -> tuple[Poly, Poly, Poly, Poly]:
    """Prima colonna di `U` e i suoi pesi, sull'anello libero."""
    law = law_ring(quotient=False)
    state = evolution(law, hamiltonian(law)).apply(
        State((law.ring.one(), law.ring.zero()))
    )
    weights = born(state)
    return state.amplitudes[0], state.amplitudes[1], weights[0], weights[1]


def axis_reading(cosine: Fraction, sine: Fraction) -> tuple[Gauss, Gauss, Gauss, Gauss]:
    """`⟨0|U|0⟩`, `⟨1|U|0⟩`, `P(0)`, `P(1)` in `(cosine, sine)` lungo `e_x`."""
    amplitude0, amplitude1, weight0, weight1 = _axis_columns()
    point = {
        "c": g(cosine),
        "s": g(sine),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    return (
        amplitude0.evaluate(point),
        amplitude1.evaluate(point),
        weight0.evaluate(point),
        weight1.evaluate(point),
    )


def angle_half_reading() -> tuple[
    Fraction,
    Fraction,
    Gauss,
    Gauss,
    Fraction,
    Fraction,
    Fraction,
    Fraction,
]:
    """`φ = 1/2`, `N = 4`: coseno, seno, ampiezze, pesi, scarto, resto."""
    point = Fraction(1, 2)
    cosine = cos_sum(4, point)
    sine = sin_sum(4, point)
    amplitude0, amplitude1, born0, born1 = axis_reading(cosine, sine)
    if born0.im or born1.im:
        raise ArithmeticError("un peso di Born non è reale")
    return (
        cosine,
        sine,
        amplitude0,
        amplitude1,
        born0.re,
        born1.re,
        circle_gap(4, point),
        remainder(4, point),
    )


def angle_at_half() -> tuple[
    Fraction, Fraction, Fraction, Fraction, Fraction, Fraction
]:
    """`φ = 1/2`, `N = 4`: coseno, seno, i due pesi letti da `U|0⟩`, scarto, resto."""
    cosine, sine, _amplitude0, _amplitude1, weight0, weight1, gap, bound = (
        angle_half_reading()
    )
    return cosine, sine, weight0, weight1, gap, bound


def born_scan(
    degree: int = DEGREE,
    samples: tuple[Fraction, ...] = SAMPLES,
) -> tuple[bool, str]:
    """Lungo `e_x`, i pesi di `U|0⟩` in `(C_N, S_N)` sono i quadrati.

    La somma dista da `1` al più del resto. L'anello è libero.
    """
    for order in range(degree + 1):
        for sample in samples:
            cosine = cos_sum(order, sample)
            sine = sin_sum(order, sample)
            if abs(circle_gap(order, sample)) > remainder(order, sample):
                return (
                    False,
                    f"scarto a N = {order}, φ = {_rat(sample)}",
                )
            amp0, amp1, born0, born1 = axis_reading(cosine, sine)
            if (
                amp0 != g(cosine)
                or amp1 != g(0, -sine)
                or born0 != g(cosine * cosine)
                or born1 != g(sine * sine)
            ):
                return (
                    False,
                    f"pesi a N = {order}, φ = {_rat(sample)}: "
                    f"{amp0}, {amp1}, {born0}, {born1}",
                )
    cosine, sine, weight0, weight1, gap, bound = angle_at_half()
    if (
        cosine != Fraction(337, 384)
        or sine != Fraction(23, 48)
        or weight0 != Fraction(113569, 147456)
        or weight1 != Fraction(529, 2304)
        or gap != Fraction(-31, 147456)
        or bound != Fraction(401, 40320)
        or abs(gap) > bound
    ):
        return (False, "il testimone non torna")
    listed = ", ".join(_rat(sample) for sample in samples)
    return (
        True,
        f"per ogni N ≤ {degree} e per φ in {{{listed}}}, anello libero\n"
        f"testimone φ = 1/2, N = 4: C = {_rat(cosine)}, S = {_rat(sine)}, "
        f"pesi {_rat(weight0)} e {_rat(weight1)}, "
        f"scarto {_rat(gap)}, resto {_rat(bound)}",
    )
