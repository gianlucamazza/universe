"""Dinamica del qubit: Φ = exp(−i φ n·σ).

H = n·σ con le matrici di Pauli standard. Sulla varietà |n| = 1 vale H² = I,
e la serie dell'esponenziale collassa nella forma chiusa

    U = c I − i s H,    c = cos φ,  s = sin φ,  φ = ω t / 2.

Quel collasso è `Universe.Qubit.expCoeff_hamiltonian`: i coefficienti coincidono
perché H² = I nel quoziente. Questo modulo costruisce la forma chiusa.
"""

from __future__ import annotations

from universe.ontology import Operator
from universe.ring import Scalars, g


def pauli(scalars: Scalars) -> tuple[Operator, Operator, Operator]:
    ring = scalars.ring
    one, zero = ring.one(), ring.zero()
    i = ring.constant(g(0, 1))
    minus_i = ring.constant(g(0, -1))
    sigma_x = Operator.from_rows([[zero, one], [one, zero]])
    sigma_y = Operator.from_rows([[zero, minus_i], [i, zero]])
    sigma_z = Operator.from_rows([[one, zero], [zero, -one]])
    return sigma_x, sigma_y, sigma_z


def hamiltonian(scalars: Scalars) -> Operator:
    sigma_x, sigma_y, sigma_z = pauli(scalars)
    return (
        sigma_x.scale(scalars.nx)
        + sigma_y.scale(scalars.ny)
        + sigma_z.scale(scalars.nz)
    )


def evolution(scalars: Scalars, generator: Operator) -> Operator:
    """Forma chiusa c I − i s H. Non è l'esponenziale simbolico: è la sua somma."""
    eye = Operator.eye(scalars.ring, generator.n)
    minus_i = scalars.ring.constant(g(0, -1))
    return eye.scale(scalars.c) + generator.scale(minus_i * scalars.s)
