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
"""

from __future__ import annotations

from universe.dynamics import hamiltonian
from universe.ontology import Operator
from universe.ring import Scalars, g


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


def closed_generator(scalars: Scalars, generated: Operator) -> Operator:
    """`(1 − G²) + c G² − i s G`. È `Universe.Interaction.closedGenerator`."""
    eye = Operator.eye(scalars.ring, generated.n)
    square = generated.matmul(generated)
    minus_i = scalars.ring.constant(g(0, -1))
    return (
        (eye - square) + square.scale(scalars.c) + generated.scale(minus_i * scalars.s)
    )
