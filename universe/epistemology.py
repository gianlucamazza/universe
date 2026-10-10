"""Epistemologia: che cosa un osservatore interno può estrarre.

Obs, per il qubit, è la misura proiettiva nella base computazionale.
La probabilità di un'ampiezza è il suo modulo quadro. Nel testo Lean il
modulo libero è `modulus_squares`, la razionalità dei coefficienti è
`modulus_imag_zero`, il proiettore `Π₀` è `projector_born`, la somma su
`Φ|0⟩` è `ground_prob_sum`, e la somma sullo stato generico è
`sphere_prob_sum`, con cofattori `gC`, `gN` e `gA`. `literal_sandwich`
identifica quel sandwich con il modulo letterale `‖Uψ‖²`. Gli assi e il punto
razionale sono nella stessa libreria. La nota è `papers/qubit.md`.
"""

from __future__ import annotations

from universe.ontology import Operator, State, tensor_index
from universe.ring import Poly, Ring


def born(state: State) -> tuple[Poly, ...]:
    return tuple(amplitude.modulus_squared() for amplitude in state.amplitudes)


def norm_squared(state: State) -> Poly:
    total = state.ring.zero()
    for amplitude in state.amplitudes:
        total = total + amplitude.modulus_squared()
    return total


def expectation(state: State, observable: Operator) -> Poly:
    if observable.n != state.dim or observable.ring is not state.ring:
        raise ValueError("osservabile incompatibile")
    image = observable.apply(state)
    total = state.ring.zero()
    for bra, ket in zip(state.amplitudes, image.amplitudes, strict=True):
        total = total + bra.conj() * ket
    return total


def computational_projector(ring: Ring, outcome: int, size: int = 2) -> Operator:
    if not 0 <= outcome < size:
        raise ValueError("esito fuori dalla base")
    rows: list[list[Poly]] = []
    for i in range(size):
        rows.append(
            [ring.one() if i == j == outcome else ring.zero() for j in range(size)]
        )
    return Operator.from_rows(rows)


def marginal(state: State, factor: int, left: int, right: int) -> tuple[Poly, ...]:
    """Probabilità di un fattore. L'indice del composto è right·i + k.

    factor 0 è il fattore sinistro, factor 1 il destro.
    """
    if state.dim != left * right:
        raise ValueError("lo stato non ha la dimensione del composto")
    if factor not in (0, 1):
        raise ValueError("fattore sconosciuto")
    outcomes = left if factor == 0 else right
    other_dim = right if factor == 0 else left
    probs: list[Poly] = []
    for outcome in range(outcomes):
        total = state.ring.zero()
        for other in range(other_dim):
            if factor == 0:
                index = tensor_index(outcome, other, right)
            else:
                index = tensor_index(other, outcome, right)
            total = total + state.amplitudes[index].modulus_squared()
        probs.append(total)
    return tuple(probs)
