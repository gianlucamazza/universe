"""Stati generici di `n` qubit e matrici su un qubit solo.

Il qubit `0` è il bit alto: l'indice della cella è `Σ bₖ 2^(n−1−k)`, come
`node` in `Universe.Qubits.QState` e come le celle di `Quad` e `Oct`.
`generic_state(n)` mette `2ⁿ` ampiezze libere `a{k}r + i a{k}i` sull'anello
della legge. `on_qubit` è `I ⊗ … ⊗ U ⊗ … ⊗ I`, `Universe.Qubits.applyAt`.
"""

from __future__ import annotations

from universe.ontology import Operator, State
from universe.ring import Law, g, law_ring


def generic_state(n: int) -> tuple[Law, State]:
    """La legge e uno stato di `n` qubit con `2ⁿ` ampiezze libere."""
    dim = 1 << n
    law = law_ring(tuple(f"a{k}{part}" for k in range(dim) for part in ("r", "i")))
    ring = law.ring
    imag = ring.constant(g(0, 1))
    state = State(
        tuple(ring.var(f"a{k}r") + ring.var(f"a{k}i") * imag for k in range(dim))
    )
    return law, state


def on_qubit(gate: Operator, qubit: int, n: int) -> Operator:
    """`gate` sul qubit `qubit` di `n`, l'identità sugli altri."""
    if not 0 <= qubit < n:
        raise ValueError(f"qubit {qubit} fuori da 0..{n - 1}")
    eye = Operator.eye(gate.ring, 2)
    factors = [gate if index == qubit else eye for index in range(n)]
    acc = factors[0]
    for factor in factors[1:]:
        acc = acc.tensor(factor)
    return acc
