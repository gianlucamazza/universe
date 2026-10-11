"""Interazione da un'Hamiltoniana su due qubit.

`G = |1⟩⟨1| ⊗ (n·σ)` sulle celle `2i + k`. Non è un'involuzione:
`G² = |1⟩⟨1| ⊗ I` nel quoziente e `G³ = G`. I coefficienti di
`exp(−i φ G)` sono `Universe.Series.expCoeff_idem`. La forma chiusa è
`|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`,
`Universe.Interaction.controlled_from_hamiltonian`.
Nel punto `c = 0`, `s = 1`, `n = e_x` si ha `U = −i X`, e su
`|ψ⟩ ⊗ |0⟩` lo stato è `α|00⟩ − i β|11⟩`
(`Universe.Interaction.cnot_point`). La fase esce da ogni peso di Born
(`Universe.Interaction.cnot_point_born`).

Con l'apparato in `|0⟩` lo stato è `α|0⟩|0⟩ + β|1⟩ U|0⟩`.
L'antidiagonale del sistema ridotto è `α β̄ · conj(⟨0|U|0⟩)`, con
`⟨0|U|0⟩ = c − i s nz` (`Universe.Interaction.partial_coherence`).
La diagonale è il peso di Born, modulo `(gC, gN)`
(`Universe.Interaction.partial_diagonal`).
"""

from __future__ import annotations

from universe.dynamics import hamiltonian
from universe.observer import reduced
from universe.ontology import Operator, State, tensor_state
from universe.ring import Poly, Scalars, g


def projector_one(scalars: Scalars) -> Operator:
    """`|1⟩⟨1| ⊗ I`. Il blocco del controllo `|0⟩` è zero."""
    one, zero = scalars.ring.one(), scalars.ring.zero()
    return Operator.from_rows(
        [
            [zero, zero, zero, zero],
            [zero, zero, zero, zero],
            [zero, zero, one, zero],
            [zero, zero, zero, one],
        ]
    )


def generator(scalars: Scalars) -> Operator:
    """`G = |1⟩⟨1| ⊗ (n·σ)`. È `Universe.Interaction.generator`."""
    block = hamiltonian(scalars)
    zero = scalars.ring.zero()
    top, bot = block.rows
    return Operator.from_rows(
        [
            [zero, zero, zero, zero],
            [zero, zero, zero, zero],
            [zero, zero, top[0], top[1]],
            [zero, zero, bot[0], bot[1]],
        ]
    )


def controlled(operator: Operator) -> Operator:
    """`|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`. È `Universe.Interaction.controlledEvolution`."""
    one, zero = operator.ring.one(), operator.ring.zero()
    top, bot = operator.rows
    return Operator.from_rows(
        [
            [one, zero, zero, zero],
            [zero, one, zero, zero],
            [zero, zero, top[0], top[1]],
            [zero, zero, bot[0], bot[1]],
        ]
    )


def partial_reduced(operator: Operator, psi: State) -> Operator:
    """Sistema ridotto dopo l'evoluzione controllata, apparato in `|0⟩`.

    Lo stato è `α|0⟩|0⟩ + β|1⟩ U|0⟩`. È `Universe.Interaction.partialState`
    seguito da `Universe.Observer.reduceLeft`.
    """
    idle = State((operator.ring.one(), operator.ring.zero()))
    coupled = controlled(operator).apply(tensor_state(psi, idle))
    return reduced(coupled, 0, 2, 2)


def coherence_factor(operator: Operator, psi: State) -> Poly:
    """`α β̄ · conj(⟨0|U|0⟩)`. È il fattore di `partial_coherence`."""
    alpha, beta = psi.amplitudes
    bracket = operator.rows[0][0]
    return alpha * beta.conj() * bracket.conj()


def closed_generator(scalars: Scalars, generated: Operator) -> Operator:
    """`(1 − G²) + c G² − i s G`. È `Universe.Interaction.closedGenerator`."""
    eye = Operator.eye(scalars.ring, generated.n)
    square = generated.matmul(generated)
    minus_i = scalars.ring.constant(g(0, -1))
    return (
        (eye - square) + square.scale(scalars.c) + generated.scale(minus_i * scalars.s)
    )
