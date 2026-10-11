"""Stati generici di `n` qubit e matrici su un qubit solo.

Il qubit `0` è il bit alto: l'indice della cella è `Σ bₖ 2^(n−1−k)`, come
`node` in `Universe.Qubits.QState` e come le celle di `Quad` e `Oct`.
`generic_state(n)` mette `2ⁿ` ampiezze libere `a{k}r + i a{k}i` sull'anello
della legge. `on_qubit` è `I ⊗ … ⊗ U ⊗ … ⊗ I`, `Universe.Qubits.applyAt`.
`marginal_at` è la coppia di Born di un qubit, `Universe.Qubits.marginalAt`.
`reduce_at` è la traccia parziale su un qubit, `Universe.Qubits.reduceAt`.
`embed_qubit` mette `|ψ⟩` su un qubit e un resto sugli altri,
`Universe.Qubits.embedAt`.
"""

from __future__ import annotations

from universe.epistemology import marginal
from universe.ontology import Operator, State
from universe.ring import Law, Poly, law_ring


def _qubit_count(dim: int) -> int:
    """`n` con `dim = 2ⁿ`."""
    if dim < 1 or dim & (dim - 1):
        raise ValueError(f"la dimensione {dim} non è una potenza di due")
    return dim.bit_length() - 1


def _check_qubit(qubit: int, n: int) -> None:
    if not 0 <= qubit < n:
        raise ValueError(f"qubit {qubit} fuori da 0..{n - 1}")


def generic_state(n: int, extra: tuple[str, ...] = ()) -> tuple[Law, State]:
    """La legge e uno stato di `n` qubit con `2ⁿ` ampiezze libere.

    `extra` aggiunge indeterminate libere sullo stesso anello.
    """
    dim = 1 << n
    amplitudes = tuple(f"a{k}{part}" for k in range(dim) for part in ("r", "i"))
    law = law_ring(amplitudes + extra)
    state = State(tuple(law.ring.complex_var(f"a{k}") for k in range(dim)))
    return law, state


def on_qubit(gate: Operator, qubit: int, n: int) -> Operator:
    """`gate` sul qubit `qubit` di `n`, l'identità sugli altri."""
    _check_qubit(qubit, n)
    eye = Operator.eye(gate.ring, 2)
    factors = [gate if index == qubit else eye for index in range(n)]
    acc = factors[0]
    for factor in factors[1:]:
        acc = acc.tensor(factor)
    return acc


def marginal_at(state: State, qubit: int) -> tuple[Poly, Poly]:
    """Coppia di Born del qubit `qubit`. Il qubit `0` è il bit alto.

    È `Universe.Qubits.marginalAt`. Ogni blocco di lunghezza `2^(n−qubit)`
    ha quel qubit come bit alto, e `marginal` somma il resto del blocco.
    """
    dim = state.dim
    n = _qubit_count(dim)
    _check_qubit(qubit, n)
    block = 1 << (n - qubit)
    half = block >> 1
    p0, p1 = state.ring.zero(), state.ring.zero()
    amplitudes = state.amplitudes
    for start in range(0, dim, block):
        weights = marginal(State(amplitudes[start : start + block]), 0, 2, half)
        p0 = p0 + weights[0]
        p1 = p1 + weights[1]
    return p0, p1


def reduce_at(state: State, qubit: int) -> Operator:
    """Traccia parziale sul qubit `qubit`. È `Universe.Qubits.reduceAt`.

    L'entrata `(a, b)` somma `ampiezza · coniugata` sugli altri bit, con
    il qubit `a` sulla riga e `b` sulla colonna.
    """
    dim = state.dim
    n = _qubit_count(dim)
    _check_qubit(qubit, n)
    ring = state.ring
    amplitudes = state.amplitudes
    shift = n - 1 - qubit
    rows: list[list[Poly]] = []
    for row_bit in (0, 1):
        row: list[Poly] = []
        for col_bit in (0, 1):
            total = ring.zero()
            for index in range(dim):
                if (index >> shift) & 1 != row_bit:
                    continue
                other = index if row_bit == col_bit else index ^ (1 << shift)
                total = total + amplitudes[index] * amplitudes[other].conj()
            row.append(total)
        rows.append(row)
    return Operator.from_rows(rows)


def embed_qubit(psi: State, rest: tuple[Poly, ...], qubit: int) -> State:
    """`|ψ⟩` sul qubit `qubit`, `rest` sugli altri. È `Universe.Qubits.embedAt`.

    `rest` ha `2^(n−1)` ampiezze. Il bit `qubit` dello stato viene da `ψ`,
    gli altri bit, nell'ordine, da `rest`.
    """
    if psi.dim != 2:
        raise ValueError("ψ ha due ampiezze")
    n = _qubit_count(len(rest)) + 1
    _check_qubit(qubit, n)
    ring = psi.ring
    if any(amplitude.ring is not ring for amplitude in rest):
        raise ValueError("anelli diversi")
    amplitudes: list[Poly] = []
    for index in range(1 << n):
        bit = (index >> (n - 1 - qubit)) & 1
        rest_index = 0
        for other in range(n):
            if other == qubit:
                continue
            rest_index = (rest_index << 1) | ((index >> (n - 1 - other)) & 1)
        amplitudes.append(psi.amplitudes[bit] * rest[rest_index])
    return State(tuple(amplitudes))
