"""Osservatore interno: CNOT, traccia parziale, purezza.

`cnot` scambia `|10⟩` e `|11⟩`, come `Universe.Observer.applyCNOT`.
`determinant_2x2` è `a0 a3 − a1 a2`, lo stesso polinomio di `quadDet`.
Su un prodotto il determinante è zero. Nel punto razionale
`CNOT(Φ|0⟩ ⊗ |0⟩)` vale `−12/25 i`, quindi non è un prodotto.

`reduced` è la traccia parziale. Il fattore `0` è `reduceLeft`, il fattore
`1` è `reduceRight`. `purity` è la traccia di `ρ²`, come
`Universe.Observer.purity`.

`cnot01` è `cnot ⊗ I` sul primo apparato. `cnot02` è la stessa porta sul
secondo, coniugata dallo scambio dei due apparati. Su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩`
restano ampiezze solo nelle celle 0 e 7.

`no_signalling_gap` è `I ⊗ U` su uno stato di due qubit generico. `U` è
`c I − i s H` nel quoziente. La differenza dei pesi del sistema ha resto
zero. Lean lo prova per ogni stato, `Universe.Observer.no_signalling_any_0`
e `Universe.Observer.no_signalling_any_1`, e su `genericQuad`,
`Universe.Observer.no_signalling_gen_0` e
`Universe.Observer.no_signalling_gen_1`. Il caso `CNOT(|ψ⟩ ⊗ |0⟩)` resta
`Universe.Observer.no_signalling_0` e `Universe.Observer.no_signalling_1`.
"""

from __future__ import annotations

from universe.dynamics import evolution, hamiltonian
from universe.epistemology import marginal
from universe.ontology import Operator, State, tensor_index
from universe.ring import Poly, Ring, Scalars, g


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


def _basis_permutation(ring: Ring, images: tuple[int, ...]) -> Operator:
    """Manda il vettore di base `e_j` in `e_{images[j]}`."""
    size = len(images)
    one, zero = ring.one(), ring.zero()
    rows = [[zero for _ in range(size)] for _ in range(size)]
    for source, target in enumerate(images):
        rows[target][source] = one
    return Operator.from_rows(rows)


def _swap_apparatuses(ring: Ring) -> Operator:
    """Scambia i due apparati.

    La cella `4 * i + 2 * j + k` va in `4 * i + 2 * k + j`.
    """
    images: list[int] = []
    for index in range(8):
        system, rest = divmod(index, 4)
        first, second = divmod(rest, 2)
        images.append(4 * system + 2 * second + first)
    return _basis_permutation(ring, tuple(images))


def cnot01(ring: Ring) -> Operator:
    """CNOT fra il sistema e il primo apparato. È `cnot ⊗ I`.

    L'indice è `4 * i + 2 * j + k`. Scambia le celle 4↔6 e 5↔7.
    È `Universe.Observer.cnot01`.
    """
    return cnot(ring).tensor(Operator.eye(ring, 2))


def cnot02(ring: Ring) -> Operator:
    """CNOT fra il sistema e il secondo apparato.

    Coniuga `cnot ⊗ I` con lo scambio dei due apparati. Scambia le celle
    4↔5 e 6↔7. È `Universe.Observer.cnot02`.
    """
    swap = _swap_apparatuses(ring)
    return swap.matmul(cnot01(ring)).matmul(swap)


def purity(operator: Operator) -> Poly:
    """Traccia di `ρ²`. È `Universe.Observer.purity`."""
    square = operator.matmul(operator)
    total = operator.ring.zero()
    for index in range(operator.n):
        total = total + square.rows[index][index]
    return total


def no_signalling_gap() -> tuple[Poly, Poly]:
    """Differenza dei pesi del sistema, prima e dopo `I ⊗ U`.

    Le quattro ampiezze sono indeterminate, su
    `(c, s, nx, ny, nz, a0r, a0i, a1r, a1i, a2r, a2i, a3r, a3i)`.
    `U = c I − i s H` usa le regole `c²` e `nx²`. `ar`, `ai`, `br`, `bi`
    non servono: lo stato porta le proprie ampiezze. È
    `Universe.Composition.genericQuad`, e i teoremi sono
    `Universe.Observer.no_signalling_gen_0` e
    `Universe.Observer.no_signalling_gen_1`.
    """
    names = (
        "c",
        "s",
        "nx",
        "ny",
        "nz",
        "a0r",
        "a0i",
        "a1r",
        "a1i",
        "a2r",
        "a2i",
        "a3r",
        "a3i",
    )
    ring = Ring(names)
    symbol = {name: ring.var(name) for name in names}
    one = ring.one()
    ring.set_square("c", one - symbol["s"] ** 2)
    ring.set_square("nx", one - symbol["ny"] ** 2 - symbol["nz"] ** 2)
    zero = ring.zero()
    scalars = Scalars(
        ring=ring,
        c=symbol["c"],
        s=symbol["s"],
        nx=symbol["nx"],
        ny=symbol["ny"],
        nz=symbol["nz"],
        ar=zero,
        ai=zero,
        br=zero,
        bi=zero,
    )
    imag = ring.constant(g(0, 1))
    state = State(tuple(symbol[f"a{k}r"] + symbol[f"a{k}i"] * imag for k in range(4)))
    local = Operator.eye(ring, 2).tensor(evolution(scalars, hamiltonian(scalars)))
    before = marginal(state, 0, 2, 2)
    after = marginal(local.apply(state), 0, 2, 2)
    return after[0] - before[0], after[1] - before[1]
