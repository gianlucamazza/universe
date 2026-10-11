"""Dinamica del qubit: Φ = exp(−i φ n·σ).

H = n·σ con Y = [[0, −i], [i, 0]]. Nel quoziente |n| = 1 vale H² = I,
e la serie dell'esponenziale collassa nella forma chiusa

    U = c I − i s H,    φ = ω t / 2.

c e s restano le indeterminate del cerchio. Nella forma chiusa si leggono
come cos φ e sin φ. Quel collasso è `Universe.Qubit.expCoeff_hamiltonian`:
i coefficienti coincidono perché H² = I nel quoziente. Questo modulo
costruisce la forma chiusa.
"""

from __future__ import annotations

from universe.ontology import Operator
from universe.ring import Law, g


def pauli(law: Law) -> tuple[Operator, Operator, Operator]:
    ring = law.ring
    one, zero = ring.one(), ring.zero()
    i = ring.constant(g(0, 1))
    minus_i = ring.constant(g(0, -1))
    sigma_x = Operator.from_rows([[zero, one], [one, zero]])
    sigma_y = Operator.from_rows([[zero, minus_i], [i, zero]])
    sigma_z = Operator.from_rows([[one, zero], [zero, -one]])
    return sigma_x, sigma_y, sigma_z


def hamiltonian(law: Law) -> Operator:
    sigma_x, sigma_y, sigma_z = pauli(law)
    return sigma_x.scale(law.nx) + sigma_y.scale(law.ny) + sigma_z.scale(law.nz)


def evolution(law: Law, generator: Operator) -> Operator:
    """Forma chiusa c I − i s H, i coefficienti dati da expCoeff_hamiltonian."""
    eye = Operator.eye(law.ring, generator.n)
    minus_i = law.ring.constant(g(0, -1))
    return eye.scale(law.c) + generator.scale(minus_i * law.s)
