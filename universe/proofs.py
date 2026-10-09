"""Teoremi del primo universo.

Ogni identità algebrica è un resto zero nel quoziente delle regole dichiarate.
Il resto zero vale quando l'espansione libera dei cofattori ridà il polinomio.
Il collasso della serie è Universe.Qubit.expCoeff_hamiltonian: H² = I nel
quoziente, quindi expCoeff si applica a H.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from universe.epistemology import (
    computational_projector,
    expectation,
    marginal,
    norm_squared,
)
from universe.ontology import Operator, State, determinant, tensor_index, tensor_state
from universe.ring import ZERO_G, Gauss, Ring, g
from universe.worlds.qubit import QubitUniverse


@dataclass(frozen=True)
class Theorem:
    section: str
    name: str
    holds: bool
    detail: str = ""


ANALYTIC_PREMISE = (
    "Universe.Qubit.expCoeff_hamiltonian: H² = I nel quoziente, quindi "
    "il coefficiente di φⁿ/n! in exp(−iφ H) è quello di cos φ · I + (−i sin φ) · H. "
    "U = c I − i s H è la forma chiusa di quel collasso."
)


def prove(world: QubitUniverse | None = None) -> list[Theorem]:
    world = world or QubitUniverse()
    scalars = world.scalars
    ring = scalars.ring
    proven: list[Theorem] = []

    def add(section: str, name: str, holds: bool, detail: str = "") -> None:
        proven.append(Theorem(section, name, holds, detail))

    def poly_zero(section: str, name: str, poly, detail: str = "") -> None:
        reason = poly.certification()
        add(section, name, reason is None, detail if reason is None else reason)

    def op_zero(section: str, name: str, operator: Operator, detail: str = "") -> None:
        reason = _first_certificate(operator)
        add(section, name, reason is None, detail if reason is None else reason)

    one = scalars.one

    # --- Calcolo: il decisore delle identità è affidabile ---
    gauss = (ring.constant(g(1, 1)) * ring.constant(g(1, -1))) - ring.constant(g(2))
    poly_zero("Calcolo", "(1+i)(1−i) = 2", gauss)

    circle = scalars.c**2 + scalars.s**2 - one
    square = circle * circle
    outside = scalars.c * scalars.s
    square_cofactors, square_zero = square.witness()
    outside_cofactors, outside_zero = outside.witness()
    audit = (
        circle.certification() is None
        and square_cofactors
        and square_zero
        and outside_cofactors
        and not outside_zero
    )
    poly_zero(
        "Calcolo",
        "c² + s² − 1 ≡ 0",
        circle,
        "cofattori: (c²+s²−1)² nell'ideale, c·s fuori"
        if audit
        else "audit del decisore fallito",
    )
    if not audit:
        proven[-1] = Theorem(
            proven[-1].section,
            proven[-1].name,
            False,
            "audit del decisore fallito",
        )

    axis = scalars.nx**2 + scalars.ny**2 + scalars.nz**2 - one
    poly_zero("Calcolo", "nx² + ny² + nz² − 1 ≡ 0", axis)

    # --- Legge ---
    eye = Operator.eye(ring, 2)
    op_zero("Legge", "H† = H", world.H.dagger() - world.H)
    op_zero("Legge", "H² = I", world.H.matmul(world.H) - eye)
    op_zero("Legge", "H³ = H", _power(world.H, 3) - world.H)
    op_zero("Legge", "H⁴ = I", _power(world.H, 4) - eye)
    op_zero("Legge", "U†U = I", world.U.dagger().matmul(world.U) - eye)
    op_zero("Legge", "UU† = I", world.U.matmul(world.U.dagger()) - eye)
    poly_zero("Legge", "det U = 1", determinant(world.U) - one)

    psi = world.generic()
    phi = world.evolve(psi)
    poly_zero(
        "Legge",
        "‖Uψ‖² = ‖ψ‖² per ogni ampiezza",
        norm_squared(phi) - norm_squared(psi),
    )

    # --- Osservazione ---
    ground = world.evolve(world.ground())
    p0, p1 = world.observe(ground)
    poly_zero(
        "Osservazione",
        "P(0) + P(1) = 1 sullo stato fondamentale evoluto",
        p0 + p1 - one,
    )

    sphere = one - (scalars.ai**2 + scalars.br**2 + scalars.bi**2)
    defect = norm_squared(phi) - one
    reason = defect.certify_extra("ar", sphere)
    bare = defect.certification()
    if reason is None and bare is not None:
        add(
            "Osservazione",
            "sulla sfera unitaria, P(0) + P(1) = 1",
            True,
            "gA = ar² + ai² + br² + bi² − 1; senza gA il resto non è zero",
        )
    else:
        add(
            "Osservazione",
            "sulla sfera unitaria, P(0) + P(1) = 1",
            False,
            reason or "la sfera non era necessaria",
        )

    q0, q1 = world.observe(phi)
    real = q0.imag_is_zero() and q1.imag_is_zero()
    add(
        "Osservazione",
        "P(0) e P(1) sono reali",
        real,
        "" if real else "parte immaginaria residua",
    )

    squares_ok = True
    squares_rest = ""
    for amplitude in phi.amplitudes:
        re, im = amplitude.real_imag()
        defect = amplitude.modulus_squared() - (re**2 + im**2)
        if not defect.is_zero():
            squares_ok = False
            squares_rest = f"resto = {defect}"
            break
    add(
        "Osservazione",
        "|z|² è la somma dei quadrati delle parti reale e immaginaria",
        squares_ok,
        squares_rest,
    )

    projector = computational_projector(ring, 0)
    alpha_mod = psi.amplitudes[0].modulus_squared()
    poly_zero(
        "Osservazione",
        "⟨ψ|Π₀|ψ⟩ = |α|²",
        expectation(psi, projector) - alpha_mod,
    )

    along_x = {"nx": g(1), "ny": g(0), "nz": g(0)}
    along_z = {"nx": g(0), "ny": g(0), "nz": g(1)}
    p0x, p1x = p0.substitute(along_x), p1.substitute(along_x)
    p0z, p1z = p0.substitute(along_z), p1.substitute(along_z)
    x_ok = p0x == (one - scalars.s**2) and p1x == (scalars.s**2)
    z_ok = p0z.is_one() and p1z.is_zero()
    add(
        "Osservazione",
        "asse x: P(0) = 1 − s², P(1) = s²",
        x_ok,
        "" if x_ok else f"P(0) = {p0x}, P(1) = {p1x}",
    )
    add(
        "Osservazione",
        "asse z: |0⟩ è autostato, P(0) = 1",
        z_ok,
        "" if z_ok else f"P(0) = {p0z}, P(1) = {p1z}",
    )

    # --- Composizione ---
    add("Composizione", *_tensor_associativity())

    pair = tensor_state(world.ground(), world.ground())
    pair_ok = (
        pair.dim == 4
        and pair.amplitudes[0].is_one()
        and all(amplitude.is_zero() for amplitude in pair.amplitudes[1:])
    )
    add("Composizione", "|0⟩ ⊗ |0⟩ = |00⟩", pair_ok)

    identity = Operator.eye(ring, 2)
    local_left = world.U.tensor(identity).apply(pair)
    left = marginal(local_left, 0, 2, 2)
    single = world.observe(world.evolve(world.ground()))
    left_ok = left[0] == single[0] and left[1] == single[1]
    add(
        "Composizione",
        "(U ⊗ I)|00⟩ riproduce le probabilità del primo fattore",
        left_ok,
        "" if left_ok else f"P = ({left[0]}, {left[1]})",
    )

    local_right = identity.tensor(world.U).apply(pair)
    right = marginal(local_right, 1, 2, 2)
    right_ok = right[0] == single[0] and right[1] == single[1]
    add(
        "Composizione",
        "(I ⊗ U)|00⟩ riproduce le probabilità del secondo fattore",
        right_ok,
        "" if right_ok else f"P = ({right[0]}, {right[1]})",
    )

    # --- Corollario razionale, cammino indipendente in aritmetica di Gauss ---
    point = {
        "c": g(Fraction(3, 5)),
        "s": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    matrix = [[entry.evaluate(point) for entry in row] for row in world.U.rows]
    product = _gauss_matmul(_gauss_dagger(matrix), matrix)
    rational_ok = _is_gauss_identity(product)
    add(
        "Corollario",
        "c = 3/5, s = 4/5, n = e_x: U†U = I nei razionali di Gauss",
        rational_ok,
        _format_matrix(matrix) if rational_ok else _format_matrix(product),
    )
    column = (matrix[0][0], matrix[1][0])
    prob0 = _modulus_sq(column[0])
    prob1 = _modulus_sq(column[1])
    probs_ok = prob0 == Fraction(9, 25) and prob1 == Fraction(16, 25)
    add(
        "Corollario",
        "nello stesso punto, P(0) = 9/25 e P(1) = 16/25",
        probs_ok,
        "" if probs_ok else f"P(0) = {prob0}, P(1) = {prob1}",
    )
    return proven


def render(theorems: list[Theorem], world: QubitUniverse) -> str:
    evolved = world.evolve(world.ground())
    alpha, beta = evolved.amplitudes
    lines = [
        "Universo — primo mondo, il qubit",
        "X = ℂ²    Φ = cos φ · I − i sin φ · (n·σ)    φ = ωt/2",
        "Vincoli del quoziente:  c² + s² = 1,   nx² + ny² + nz² = 1",
        f"Φ|0⟩ = ({alpha}, {beta})",
        "",
    ]
    section = ""
    passed = 0
    for theorem in theorems:
        if theorem.section != section:
            section = theorem.section
            lines.append(section)
        mark = "dimostrato" if theorem.holds else "FALLITO"
        lines.append(f"  [{mark}] {theorem.name}")
        if theorem.detail:
            for detail in theorem.detail.splitlines():
                lines.append(f"             {detail}")
        if theorem.holds:
            passed += 1
    lines.append("")
    lines.append(f"{passed}/{len(theorems)} identità algebriche dimostrate.")
    lines.append("")
    lines.append("Collasso della serie, teorema Universe.Series.expCoeff")
    lines.append(f"  {ANALYTIC_PREMISE}")
    return "\n".join(lines)


def main() -> int:
    world = QubitUniverse()
    theorems = prove(world)
    print(render(theorems, world))
    return 0 if all(theorem.holds for theorem in theorems) else 1


def _tensor_associativity() -> tuple[str, bool, str]:
    """Identità libera di `tensor_index`, dunque Universe.Ontology.tensorIndexAssoc."""
    ring = Ring(("i", "j", "k", "nb", "nc"))
    i, j, k, nb, nc = (ring.var(name) for name in ring.variables)
    left = (i * nb + j) * nc + k
    right = i * (nb * nc) + (j * nc + k)
    defect = left - right
    layout = _tensor_layout()
    if defect.is_zero() and layout:
        return (
            "(A⊗B)⊗C e A⊗(B⊗C) hanno la stessa codifica di indici",
            True,
            "tensor_index; identità polinomiale, dunque Nat come tensorIndexAssoc",
        )
    detail = f"resto = {defect}" if not defect.is_zero() else "layout di tensor_state"
    return (
        "(A⊗B)⊗C e A⊗(B⊗C) hanno la stessa codifica di indici",
        False,
        detail,
    )


def _tensor_layout() -> bool:
    ring = Ring(("e",))

    def basis(index: int, dim: int) -> State:
        return State(
            tuple(ring.one() if j == index else ring.zero() for j in range(dim))
        )

    compound = tensor_state(basis(1, 2), basis(2, 3))
    expect = tensor_index(1, 2, 3)
    return (
        compound.dim == 6
        and compound.amplitudes[expect].is_one()
        and all(
            amplitude.is_zero()
            for i, amplitude in enumerate(compound.amplitudes)
            if i != expect
        )
    )


def _power(operator: Operator, n: int) -> Operator:
    result = Operator.eye(operator.ring, operator.n)
    for _ in range(n):
        result = operator.matmul(result)
    return result


def _first_certificate(operator: Operator) -> str | None:
    for i, row in enumerate(operator.rows):
        for j, entry in enumerate(row):
            reason = entry.certification()
            if reason is not None:
                return f"({i},{j}): {reason}"
    return None


def _gauss_dagger(matrix: list[list[Gauss]]) -> list[list[Gauss]]:
    size = len(matrix)
    return [[matrix[j][i].conj() for j in range(size)] for i in range(size)]


def _gauss_matmul(
    left: list[list[Gauss]], right: list[list[Gauss]]
) -> list[list[Gauss]]:
    size = len(left)
    product: list[list[Gauss]] = []
    for i in range(size):
        row: list[Gauss] = []
        for j in range(size):
            total = ZERO_G
            for k in range(size):
                total += left[i][k] * right[k][j]
            row.append(total)
        product.append(row)
    return product


def _is_gauss_identity(matrix: list[list[Gauss]]) -> bool:
    size = len(matrix)
    for i in range(size):
        for j in range(size):
            expected = g(1) if i == j else g(0)
            if matrix[i][j] != expected:
                return False
    return True


def _modulus_sq(value: Gauss) -> Fraction:
    squared = value * value.conj()
    if squared.im != 0:
        raise ValueError("modulo quadro non reale")
    return squared.re


def _format_matrix(matrix: list[list[Gauss]]) -> str:
    rendered = [[_format_gauss(entry) for entry in row] for row in matrix]
    return "\n".join("[" + "   ".join(row) + "]" for row in rendered)


def _format_gauss(value: Gauss) -> str:
    if value.im == 0:
        return str(value.re)
    if value.re == 0:
        if value.im == 1:
            return "i"
        if value.im == -1:
            return "−i"
        return f"{value.im} i"
    sign = "+" if value.im > 0 else "−"
    imag = abs(value.im)
    imag_s = "i" if imag == 1 else f"{imag} i"
    return f"{value.re}{sign}{imag_s}"
