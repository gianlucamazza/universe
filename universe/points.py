"""Tabella dei punti razionali, dagli stessi conti del certificato.

`p0` è `Universe.Epistemology.point_prob0`.
`p1` è `Universe.Epistemology.point_prob1`.
"""

from __future__ import annotations

from fractions import Fraction

from universe.proofs import corollary_matrix, modulus_gauss
from universe.worlds.qubit import QubitUniverse


def points(world: QubitUniverse | None = None) -> dict[str, tuple[Fraction, Fraction]]:
    """`chiave → (re, im)` nel punto del corollario."""
    world = world or QubitUniverse()
    matrix = corollary_matrix(world)
    # Universe.Epistemology.point_prob0
    weight0 = modulus_gauss(matrix[0][0])
    # Universe.Epistemology.point_prob1
    weight1 = modulus_gauss(matrix[1][0])
    return {
        "p0": (weight0.re, weight0.im),
        "p1": (weight1.re, weight1.im),
    }
