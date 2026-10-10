"""Ontologia: stati, operatori, composizione.

X è uno spazio di Hilbert a dimensione finita. Due sistemi si compongono con il
prodotto tensoriale. L'indice di |i⟩⊗|k⟩ è `tensor_index`, la stessa formula di
`Universe.Composition.tensorIndex` e il passo binario di
`Universe.Ontology.tensorIndexAssoc`. `(A⊗B)⊗C` e `A⊗(B⊗C)` sono lo stesso
stato: le ampiezze sono `Universe.Composition.tensor_assoc`, l'azione sul
primo fattore è `tensor_assoc_ui`, i moduli quadri sono `tensor_assoc_obs`.
`|0⟩ ⊗ |0⟩ = |00⟩` è `ground_tensor`. I marginali con un fattore `|0⟩` fermo
sono `marginal_ui` e `marginal_iu`. La nota è `papers/qubit.md`.
L'argomento dell'associazione è `researches/associazione.md`.
"""

from __future__ import annotations

from dataclasses import dataclass

from universe.ring import Poly, Ring


@dataclass(frozen=True)
class State:
    amplitudes: tuple[Poly, ...]

    def __post_init__(self) -> None:
        if not self.amplitudes:
            raise ValueError("stato vuoto")
        ring = self.ring
        for amplitude in self.amplitudes:
            if amplitude.ring is not ring:
                raise ValueError("anelli diversi")

    @property
    def ring(self) -> Ring:
        return self.amplitudes[0].ring

    @property
    def dim(self) -> int:
        return len(self.amplitudes)


def tensor_index(left_index: int, right_index: int, right_dim: int) -> int:
    """Indice di |i⟩⊗|k⟩. È `Universe.Ontology.tensorIndexAssoc` sui naturali."""
    return right_dim * left_index + right_index


def tensor_index_assoc(i: int, j: int, k: int, nb: int, nc: int) -> bool:
    """`(A⊗B)⊗C` e `A⊗(B⊗C)` codificano la stessa cella.

    Le ampiezze di tre qubit, sullo stesso passo, sono
    `Universe.Composition.tensor_assoc`.
    """
    left = tensor_index(tensor_index(i, j, nb), k, nc)
    right = tensor_index(i, tensor_index(j, k, nc), nb * nc)
    return left == right


def tensor_state(left: State, right: State) -> State:
    if left.ring is not right.ring:
        raise ValueError("anelli diversi")
    width = right.dim
    amplitudes = [left.ring.zero()] * (left.dim * width)
    for i, amplitude in enumerate(left.amplitudes):
        for k, other in enumerate(right.amplitudes):
            amplitudes[tensor_index(i, k, width)] = amplitude * other
    return State(tuple(amplitudes))


@dataclass(frozen=True)
class Operator:
    rows: tuple[tuple[Poly, ...], ...]

    def __post_init__(self) -> None:
        size = len(self.rows)
        if size == 0 or any(len(row) != size for row in self.rows):
            raise ValueError("serve un operatore quadrato")
        ring = self.ring
        for row in self.rows:
            for entry in row:
                if entry.ring is not ring:
                    raise ValueError("anelli diversi")

    @property
    def ring(self) -> Ring:
        return self.rows[0][0].ring

    @property
    def n(self) -> int:
        return len(self.rows)

    @staticmethod
    def from_rows(rows: list[list[Poly]]) -> Operator:
        return Operator(tuple(tuple(row) for row in rows))

    @staticmethod
    def eye(ring: Ring, size: int) -> Operator:
        rows: list[list[Poly]] = []
        for i in range(size):
            rows.append([ring.one() if i == j else ring.zero() for j in range(size)])
        return Operator.from_rows(rows)

    def __add__(self, other: Operator) -> Operator:
        self._match(other)
        rows = tuple(
            tuple(a + b for a, b in zip(left, right, strict=True))
            for left, right in zip(self.rows, other.rows, strict=True)
        )
        return Operator(rows)

    def __sub__(self, other: Operator) -> Operator:
        return self + (-other)

    def __neg__(self) -> Operator:
        rows = tuple(tuple(-entry for entry in row) for row in self.rows)
        return Operator(rows)

    def scale(self, factor: Poly) -> Operator:
        if factor.ring is not self.ring:
            raise ValueError("anelli diversi")
        rows = tuple(tuple(factor * entry for entry in row) for row in self.rows)
        return Operator(rows)

    def matmul(self, other: Operator) -> Operator:
        """Prodotto di matrici. `self.matmul(other)` applica prima other."""
        self._match(other)
        size = self.n
        zero = self.ring.zero()
        rows: list[tuple[Poly, ...]] = []
        for i in range(size):
            row: list[Poly] = []
            for j in range(size):
                total = zero
                for k in range(size):
                    total = total + self.rows[i][k] * other.rows[k][j]
                row.append(total)
            rows.append(tuple(row))
        return Operator(tuple(rows))

    def dagger(self) -> Operator:
        size = self.n
        rows = tuple(
            tuple(self.rows[i][j].conj() for i in range(size)) for j in range(size)
        )
        return Operator(rows)

    def apply(self, state: State) -> State:
        if state.ring is not self.ring or state.dim != self.n:
            raise ValueError("stato incompatibile")
        zero = self.ring.zero()
        amplitudes: list[Poly] = []
        for i in range(self.n):
            total = zero
            for j in range(self.n):
                total = total + self.rows[i][j] * state.amplitudes[j]
            amplitudes.append(total)
        return State(tuple(amplitudes))

    def tensor(self, other: Operator) -> Operator:
        if self.ring is not other.ring:
            raise ValueError("anelli diversi")
        left, right = self.n, other.n
        rows: list[tuple[Poly, ...]] = []
        for index in range(left * right):
            i, k = divmod(index, right)
            row: list[Poly] = []
            for column in range(left * right):
                j, m = divmod(column, right)
                row.append(self.rows[i][j] * other.rows[k][m])
            rows.append(tuple(row))
        return Operator(tuple(rows))

    def _match(self, other: Operator) -> None:
        if self.ring is not other.ring or self.n != other.n:
            raise ValueError("operatori incompatibili")


def _minor(operator: Operator, drop_row: int, drop_col: int) -> Operator:
    rows = [
        [entry for j, entry in enumerate(row) if j != drop_col]
        for i, row in enumerate(operator.rows)
        if i != drop_row
    ]
    return Operator.from_rows(rows)


def determinant(operator: Operator) -> Poly:
    """Sviluppo di Laplace sulla prima riga. In dimensione 2 è `ad − bc`."""
    size = operator.n
    if size == 1:
        return operator.rows[0][0]
    total = operator.ring.zero()
    sign = 1
    for col, entry in enumerate(operator.rows[0]):
        term = entry * determinant(_minor(operator, 0, col))
        total = total + term if sign > 0 else total - term
        sign = -sign
    return total
