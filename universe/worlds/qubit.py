"""Primo universo: un qubit.

X è ℂ². La legge è Φ = c I − i s (n·σ), con c² + s² = 1 e |n| = 1.
Obs è la misura nella base computazionale.
"""

from __future__ import annotations

from universe.dynamics import evolution, hamiltonian
from universe.epistemology import born
from universe.ontology import Operator, State
from universe.ring import Poly, Scalars, g, qubit_scalars


class QubitUniverse:
    """Universo chiuso, esatto dentro i propri assiomi."""

    def __init__(self) -> None:
        self.scalars: Scalars = qubit_scalars()
        self.H: Operator = hamiltonian(self.scalars)
        self.U: Operator = evolution(self.scalars, self.H)

    def ground(self) -> State:
        """|0⟩, il punto base di X."""
        scalars = self.scalars
        return State((scalars.one, scalars.zero))

    def generic(self) -> State:
        """Punto generico di X. Le ampiezze sono indeterminate, non normalizzate."""
        scalars = self.scalars
        i = scalars.ring.constant(g(0, 1))
        alpha = scalars.ar + scalars.ai * i
        beta = scalars.br + scalars.bi * i
        return State((alpha, beta))

    def evolve(self, state: State) -> State:
        """Applica Φ."""
        return self.U.apply(state)

    def observe(self, state: State) -> tuple[Poly, ...]:
        """Estrae Obs nella base computazionale."""
        return born(state)
