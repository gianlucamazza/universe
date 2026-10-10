"""Osservatore interno: CNOT e il primo stato entangled.

`cnot` scambia `|10⟩` e `|11⟩`, come `Universe.Observer.applyCNOT`.
`determinant_2x2` è `a0 a3 − a1 a2`, lo stesso polinomio di `quadDet`.
Su un prodotto il determinante è zero. Nel punto razionale
`CNOT(Φ|0⟩ ⊗ |0⟩)` vale `−12/25 i`, quindi non è un prodotto.
"""

from __future__ import annotations

from universe.ontology import Operator, State
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
