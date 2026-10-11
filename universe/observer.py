"""Osservatore interno: CNOT, traccia parziale, purezza.

`cnot` scambia `|10⟩` e `|11⟩`, come `Universe.Observer.applyCNOT`.
`determinant_2x2` è `a0 a3 − a1 a2`, lo stesso polinomio di `quadDet`.
Su un prodotto il determinante è zero. Nel punto razionale
`CNOT(Φ|0⟩ ⊗ |0⟩)` vale `−12/25 i`, quindi non è un prodotto.

`reduced` è la traccia parziale. Il fattore `0` è `reduceLeft`, il fattore
`1` è `reduceRight`. `purity` è la traccia di `ρ²`, come
`Universe.Observer.purity`.
"""

from __future__ import annotations

from universe.ontology import Operator, State, tensor_index
from universe.ring import Poly, Ring


def cnot(ring: Ring) -> Operator:
    """CNOT con controllo a sinistra e bersaglio a destra.

    L'indice è `2 * i + k`. La matrice scambia le righe `|10⟩` e `|11⟩`.
    È `Universe.Observer.applyCNOT`.
    """
    one, zero = ring.one(), ring.zero()
    return Operator.from_rows(
        [
            [one, zero, zero, zero],
            [zero, one, zero, zero],
            [zero, zero, zero, one],
            [zero, zero, one, zero],
        ]
    )


def determinant_2x2(state: State) -> Poly:
    """`a0 a3 − a1 a2` sulle quattro ampiezze. È `Universe.Observer.quadDet`."""
    if state.dim != 4:
        raise ValueError("il determinante chiede quattro ampiezze")
    a0, a1, a2, a3 = state.amplitudes
    return a0 * a3 - a1 * a2


def reduced(state: State, factor: int, left: int, right: int) -> Operator:
    """Traccia parziale di un composto. L'indice è `right · i + k`.

    `factor` 0 tiene il fattore sinistro, come `Universe.Observer.reduceLeft`.
    `factor` 1 tiene il fattore destro, come `Universe.Observer.reduceRight`.
    L'entrata `(i, j)` somma `ampiezza · coniugata` sull'indice tracciato.
    """
    if state.dim != left * right:
        raise ValueError("lo stato non ha la dimensione del composto")
    if factor not in (0, 1):
        raise ValueError("fattore sconosciuto")
    ring = state.ring
    if factor == 0:
        size, hidden = left, right

        def index(outcome: int, other: int) -> int:
            return tensor_index(outcome, other, right)

    else:
        size, hidden = right, left

        def index(outcome: int, other: int) -> int:
            return tensor_index(other, outcome, right)

    rows: list[list[Poly]] = []
    for i in range(size):
        row: list[Poly] = []
        for j in range(size):
            total = ring.zero()
            for k in range(hidden):
                total = (
                    total
                    + state.amplitudes[index(i, k)]
                    * state.amplitudes[index(j, k)].conj()
                )
            row.append(total)
        rows.append(row)
    return Operator.from_rows(rows)


def purity(operator: Operator) -> Poly:
    """Traccia di `ρ²`. È `Universe.Observer.purity`."""
    square = operator.matmul(operator)
    total = operator.ring.zero()
    for index in range(operator.n):
        total = total + square.rows[index][index]
    return total
