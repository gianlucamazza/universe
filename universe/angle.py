"""Somme parziali di coseno e seno su un razionale.

`c_term(k, x)` è `cos_coeff(k) · xᵏ / k!`, `s_term` il seno.
`cos_sum` e `sin_sum` sommano fino al grado `n`. Non è un limite.
La convoluzione fino a `m` è il termine in `x + y`:
`Universe.Angle.angle_add_cos`, `Universe.Angle.angle_add_sin`.
`exp_term` è `xᵐ / m!`: la stessa legge è `Universe.Angle.exp_add`.
`C_n² + S_n² − 1` è `tail_sum`, e il valore assoluto sta sotto
`remainder` (`Universe.Angle.circle_tail`, `Universe.Angle.circle_bound`).
I coefficienti ripetono `Universe.Series.cosCoeff` e
`Universe.Series.sinCoeff`.
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial

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
    witness_x, witness_y = Fraction(1, 2), Fraction(3, 5)
    listed = ", ".join(_rat(sample) for sample in samples)
    cos_two = _rat(cos_conv(2, witness_x, witness_y))
    sin_three = _rat(sin_conv(3, witness_x, witness_y))
    return (
        True,
        f"per ogni m ≤ {degree} e per x, y in {{{listed}}}\n"
        f"testimone x = {_rat(witness_x)}, y = {_rat(witness_y)}: "
        f"grado 2, cos {cos_two}; grado 3, sin {sin_three}",
    )


def exp_term(m: int, x: Fraction) -> Fraction:
    """Termine `xᵐ / m!`."""
    return x**m / factorial(m)


def tail_sum(n: int, x: Fraction) -> Fraction:
    """Coda oltre il grado `n`: `Σ_{m = n + 1}^{2n} Σ_{k = m − n}^{n}` del prodotto."""
    total = Fraction(0)
    for degree in range(n + 1, 2 * n + 1):
        for index in range(degree - n, n + 1):
            total += c_term(index, x) * c_term(degree - index, x) + s_term(
                index, x
            ) * s_term(degree - index, x)
    return total


def remainder(n: int, x: Fraction) -> Fraction:
    """`r_n(x) = Σ_{m = n + 1}^{2n} (2|x|)ᵐ / m!`."""
    scale = 2 * abs(x)
    return sum(
        (exp_term(degree, scale) for degree in range(n + 1, 2 * n + 1)),
        Fraction(0),
    )


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
