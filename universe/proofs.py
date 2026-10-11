"""Certificato eseguibile del primo universo. Stampa 36 righe.

Una riga è dimostrata quando il resto è zero e l'espansione libera dei
cofattori ridà il polinomio. Il collasso della serie, nel footer, è
`Universe.Qubit.expCoeff_hamiltonian`.

La ripartizione per ideali è `papers/qubit.md`. La completezza di
`Universe.Quotient.reduce` è `Universe.Dynamics.reduce_complete`. Queste
righe restano il testimone eseguibile: resto zero e ricostruzione libera.
L'indice dei lemmi è il README. `literal_sandwich` dà al modulo letterale
`‖Uψ‖²` gli stessi coefficienti del sandwich. Questo file, sul procedimento: riduce
`‖Uψ‖² − ‖ψ‖²`; sulla sfera usa `certify_extra` per `‖Uψ‖² − 1`;
sostituisce `nx`, `ny`, `nz` nei pesi di Born, gli stessi polinomi di
`axis_x_born0` e `axis_z_born0`; moltiplica la matrice
numerica nel punto `c = 3/5`, `s = 4/5`, `n = e_x` e, sullo stesso
punto, i pesi delle otto celle di tre copie di `Φ|0⟩`; confronta i polinomi
ridotti dei marginali nel caso `|φ⟩ = |0⟩`. `|00⟩` è il caso `α = 1`,
`β = 0`. Il fattore `‖φ‖²` e il cofattore `gA` stanno in
`marginal_left_gen` e `marginal_left_sphere`. La riga di associatività
confronta gli indici sull'anello `(i, j, k, nb, nc)` e le ampiezze con
`(U ⊗ I ⊗ I)` sull'anello `(u00, u01, u10, u11, a0, a1, b0, b1, c0, c1)`.
Il dettaglio cita `tensor_assoc`, `tensor_assoc_ui` e `tensor_assoc_obs`.
La sezione Osservatore costruisce CNOT su un anello di otto reali, il
determinante di un prodotto su un altro anello fresco, e il determinante
di CNOT(Φ|0⟩ ⊗ |0⟩) nel punto c = 3/5, s = 4/5, n = e_x. I nomi sono
`Universe.Observer.cnot_involutive`, `Universe.Observer.cnot_norm`,
`Universe.Observer.product_det`, `Universe.Observer.entangled_det`,
`Universe.Observer.point_entangled` e `Universe.Observer.point_not_product`.
Dopo CNOT la traccia parziale del sistema ha antidiagonale zero e
diagonale di Born (`Universe.Observer.decoherence`); prima, l'entrata
è α β̄ (`Universe.Observer.coherence_before`). L'apparato legge gli
stessi pesi su Φ|0⟩ e sullo stato generico
(`Universe.Observer.pointer_born`). Nel punto la purezza è 337/625
(`Universe.Observer.point_purity`). `Universe.Observer.reduceLeft_diag`,
`Universe.Observer.reduce_product`, `Universe.Observer.purity_before` e
`Universe.Observer.purity_sphere` restano solo in Lean. Due apparati, in
entrambi gli ordini e su entrambe le parentesizzazioni, danno
α|000⟩ + β|111⟩: le celle 1–6 hanno peso zero
(`Universe.Observer.two_pointers`, `Universe.Observer.observers_agree`,
`Universe.Observer.order_irrelevant`). Un unitario locale sull'apparato
non cambia i due pesi del sistema. Il conto sta sull'anello
`(c, s, nx, ny, nz, a0r, a0i, a1r, a1i, a2r, a2i, a3r, a3i)`: lo stato è
generico. Lean lo prova per ogni `Quad`,
`Universe.Observer.no_signalling_any_0` e
`Universe.Observer.no_signalling_any_1`, e su `genericQuad`,
`Universe.Observer.no_signalling_gen_0` e
`Universe.Observer.no_signalling_gen_1`.
`UH = HU` ha origine libera zero
(`Universe.Symmetry.evolution_commutes_hamiltonian`).
`⟨Uψ|H|Uψ⟩ − ⟨ψ|H|ψ⟩` ha resto zero in `(gC, gN)`
(`Universe.Symmetry.energy_conserved`). Nel punto `c = 3/5`, `s = 4/5`,
`ψ = |0⟩` l'energia vale `0` lungo `e_x` e `1` lungo `e_z`, prima e dopo
`Φ` (`Universe.Symmetry.point_energy_x`, `Universe.Symmetry.point_energy_z`).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from universe.epistemology import (
    born,
    computational_projector,
    expectation,
    marginal,
    norm_squared,
)
from universe.observer import (
    cnot,
    cnot01,
    cnot02,
    determinant_2x2,
    no_signalling_gap,
    purity,
    reduced,
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

    commute = world.U.matmul(world.H) - world.H.matmul(world.U)
    commute_free = _free_zero(commute)
    commute_cert = _first_certificate(commute)
    add(
        "Legge",
        "UH = HU nell'anello libero",
        commute_free and commute_cert is None,
        "Universe.Symmetry.evolution_commutes_hamiltonian"
        if commute_free and commute_cert is None
        else (commute_cert or "l'origine libera non è zero"),
    )
    poly_zero(
        "Legge",
        "⟨Uψ|H|Uψ⟩ = ⟨ψ|H|ψ⟩",
        expectation(phi, world.H) - expectation(psi, world.H),
        "stato generico\nUniverse.Symmetry.energy_conserved",
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

    psi = world.generic()
    idle = world.ground()
    identity = Operator.eye(ring, 2)
    evolved = world.observe(world.evolve(psi))
    ground_evolved = world.observe(world.evolve(idle))
    detail = "|00⟩ è il caso α = 1, β = 0"

    local_left = world.U.tensor(identity).apply(tensor_state(psi, idle))
    left = marginal(local_left, 0, 2, 2)
    left_ground = marginal(world.U.tensor(identity).apply(pair), 0, 2, 2)
    left_ok = (
        left[0] == evolved[0]
        and left[1] == evolved[1]
        and left_ground[0] == ground_evolved[0]
        and left_ground[1] == ground_evolved[1]
    )
    add(
        "Composizione",
        "(U ⊗ I)(|ψ⟩ ⊗ |0⟩) riproduce le probabilità del primo fattore",
        left_ok,
        detail if left_ok else f"P = ({left[0]}, {left[1]})",
    )

    local_right = identity.tensor(world.U).apply(tensor_state(idle, psi))
    right = marginal(local_right, 1, 2, 2)
    right_ground = marginal(identity.tensor(world.U).apply(pair), 1, 2, 2)
    right_ok = (
        right[0] == evolved[0]
        and right[1] == evolved[1]
        and right_ground[0] == ground_evolved[0]
        and right_ground[1] == ground_evolved[1]
    )
    add(
        "Composizione",
        "(I ⊗ U)(|0⟩ ⊗ |ψ⟩) riproduce le probabilità del secondo fattore",
        right_ok,
        detail if right_ok else f"P = ({right[0]}, {right[1]})",
    )

    # --- Osservatore: CNOT e il primo stato entangled ---
    gate_ring = Ring(())
    gate = cnot(gate_ring)
    square = gate.matmul(gate)
    eye4 = Operator.eye(gate_ring, 4)
    add(
        "Osservatore",
        "CNOT² = I",
        square.rows == eye4.rows,
        "Universe.Observer.cnot_involutive",
    )

    quad_ring = Ring(("a0r", "a0i", "a1r", "a1i", "a2r", "a2i", "a3r", "a3i"))
    imag = quad_ring.constant(g(0, 1))

    def camp(index: int):
        return quad_ring.var(f"a{index}r") + quad_ring.var(f"a{index}i") * imag

    generic_quad = State(tuple(camp(index) for index in range(4)))
    quad_gate = cnot(quad_ring)
    norm_ok = norm_squared(quad_gate.apply(generic_quad)) == norm_squared(generic_quad)
    add(
        "Osservatore",
        "‖CNOT v‖² = ‖v‖² su uno stato generico",
        norm_ok,
        "anello (a0r, a0i, a1r, a1i, a2r, a2i, a3r, a3i)\nUniverse.Observer.cnot_norm",
    )

    factor_ring = Ring(("p0r", "p0i", "p1r", "p1i", "q0r", "q0i", "q1r", "q1i"))
    factor_i = factor_ring.constant(g(0, 1))

    def factor_amp(prefix: str, index: int):
        return (
            factor_ring.var(f"{prefix}{index}r")
            + factor_ring.var(f"{prefix}{index}i") * factor_i
        )

    psi_factor = State((factor_amp("p", 0), factor_amp("p", 1)))
    phi_factor = State((factor_amp("q", 0), factor_amp("q", 1)))
    product_det_ok = determinant_2x2(tensor_state(psi_factor, phi_factor)).is_zero()
    add(
        "Osservatore",
        "|ψ⟩ ⊗ |φ⟩ ha determinante zero",
        product_det_ok,
        "Universe.Observer.product_det, Universe.Observer.entangled_det",
    )

    rational = {
        "c": g(Fraction(3, 5)),
        "s": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    coupled = cnot(ring).apply(tensor_state(ground, world.ground()))
    det_point = determinant_2x2(coupled).evaluate(rational)
    point_ok = det_point == g(0, Fraction(-12, 25))
    add(
        "Osservatore",
        "nel punto razionale, det CNOT(Φ|0⟩ ⊗ |0⟩) = −12/25 i",
        point_ok,
        "non è un prodotto\n"
        "Universe.Observer.point_entangled, Universe.Observer.point_not_product"
        if point_ok
        else f"det = {det_point}",
    )

    coh_ring = Ring(("p0r", "p0i", "p1r", "p1i"))
    coh_i = coh_ring.constant(g(0, 1))
    alpha = coh_ring.var("p0r") + coh_ring.var("p0i") * coh_i
    beta = coh_ring.var("p1r") + coh_ring.var("p1i") * coh_i
    psi_coh = State((alpha, beta))
    ket = State((coh_ring.one(), coh_ring.zero()))
    product = tensor_state(psi_coh, ket)
    before = reduced(product, 0, 2, 2)
    after = reduced(cnot(coh_ring).apply(product), 0, 2, 2)
    weights = born(psi_coh)
    decoherence_ok = (
        before.rows[0][1] == alpha * beta.conj()
        and after.rows[0][1].is_zero()
        and after.rows[1][0].is_zero()
        and after.rows[0][0] == weights[0]
        and after.rows[1][1] == weights[1]
    )
    add(
        "Osservatore",
        "dopo CNOT il sistema ridotto è diagonale, con i pesi di Born",
        decoherence_ok,
        "prima, l'antidiagonale è α β̄\n"
        "Universe.Observer.decoherence, Universe.Observer.coherence_before",
    )

    def _pointer(state: State) -> bool:
        idle = State((state.ring.one(), state.ring.zero()))
        apparatus = reduced(cnot(state.ring).apply(tensor_state(state, idle)), 1, 2, 2)
        diagonal = born(state)
        return (
            apparatus.rows[0][1].is_zero()
            and apparatus.rows[1][0].is_zero()
            and apparatus.rows[0][0] == diagonal[0]
            and apparatus.rows[1][1] == diagonal[1]
        )

    pointer_ok = _pointer(ground) and _pointer(phi)
    add(
        "Osservatore",
        "l'apparato legge P(Φ|ψ⟩) su |0⟩ e sullo stato generico",
        pointer_ok,
        "Obs è la diagonale\nUniverse.Observer.pointer_born",
    )

    purity_value = purity(reduced(coupled, 0, 2, 2)).evaluate(rational)
    purity_ok = purity_value == g(Fraction(337, 625))
    add(
        "Osservatore",
        "nel punto, la purezza del sistema ridotto è 337/625",
        purity_ok,
        "337/625 < 1, stato ridotto misto\nUniverse.Observer.point_purity"
        if purity_ok
        else f"purezza = {purity_value}",
    )

    agree_ring = Ring(("p0r", "p0i", "p1r", "p1i"))
    agree_i = agree_ring.constant(g(0, 1))
    agree_alpha = agree_ring.var("p0r") + agree_ring.var("p0i") * agree_i
    agree_beta = agree_ring.var("p1r") + agree_ring.var("p1i") * agree_i
    agree_psi = State((agree_alpha, agree_beta))
    agree_ket = State((agree_ring.one(), agree_ring.zero()))
    agree_zero = agree_ring.zero()
    prepared_left = tensor_state(tensor_state(agree_psi, agree_ket), agree_ket)
    prepared_right = tensor_state(agree_psi, tensor_state(agree_ket, agree_ket))
    first_observer = cnot01(agree_ring)
    second_observer = cnot02(agree_ring)
    ghz = second_observer.apply(first_observer.apply(prepared_left))
    expected_ghz = (
        agree_alpha,
        agree_zero,
        agree_zero,
        agree_zero,
        agree_zero,
        agree_zero,
        agree_zero,
        agree_beta,
    )
    ghz_weights = born(ghz)
    agree_ok = (
        ghz.amplitudes == expected_ghz
        and first_observer.apply(second_observer.apply(prepared_left)).amplitudes
        == expected_ghz
        and second_observer.apply(first_observer.apply(prepared_right)).amplitudes
        == expected_ghz
        and first_observer.apply(second_observer.apply(prepared_right)).amplitudes
        == expected_ghz
        and ghz_weights[0] == agree_alpha.modulus_squared()
        and ghz_weights[7] == agree_beta.modulus_squared()
        and all(weight.is_zero() for weight in ghz_weights[1:7])
    )
    add(
        "Osservatore",
        "due osservatori non sono mai in disaccordo",
        agree_ok,
        "α|000⟩ + β|111⟩, celle 1–6 nulle\n"
        "Universe.Observer.two_pointers, Universe.Observer.observers_agree,\n"
        "Universe.Observer.order_irrelevant, Universe.Observer.two_pointers_right,\n"
        "Universe.Observer.observers_agree_right, Universe.Observer.order_irrelevant_right"
        if agree_ok
        else "le due porte non coincidono",
    )

    gap0, gap1 = no_signalling_gap()
    gap0_reason = gap0.certification()
    gap1_reason = gap1.certification()
    signal_ok = gap0_reason is None and gap1_reason is None
    add(
        "Osservatore",
        "un unitario locale sull'apparato non cambia i pesi del sistema",
        signal_ok,
        "stato generico, anello (c, s, nx, ny, nz, a0r, …, a3i)\n"
        "Universe.Observer.no_signalling_gen_0, Universe.Observer.no_signalling_gen_1"
        if signal_ok
        else (gap0_reason or gap1_reason or ""),
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
    factor = world.evolve(world.ground())
    triple_left = tensor_state(tensor_state(factor, factor), factor)
    triple_right = tensor_state(factor, tensor_state(factor, factor))
    cell_weights = [
        _real_fraction(weight.evaluate(point)) for weight in born(triple_left)
    ]
    cell_right = [
        _real_fraction(weight.evaluate(point)) for weight in born(triple_right)
    ]
    expected_cells = [
        Fraction(9, 25) ** (3 - (index.bit_count()))
        * Fraction(16, 25) ** index.bit_count()
        for index in range(8)
    ]
    cells_ok = cell_weights == expected_cells and cell_right == expected_cells
    cells_ok = cells_ok and sum(cell_weights) == 1
    probs_ok = prob0 == Fraction(9, 25) and prob1 == Fraction(16, 25) and cells_ok
    cell_detail = " ".join(
        f"{index}:{_format_fraction(weight)}"
        for index, weight in enumerate(cell_weights)
    )
    add(
        "Corollario",
        "nello stesso punto, P(0) = 9/25 e P(1) = 16/25",
        probs_ok,
        cell_detail
        if probs_ok
        else f"P(0) = {prob0}, P(1) = {prob1}; celle = {cell_detail}",
    )
    ket = world.ground()
    evolved_ket = world.evolve(ket)
    point_z = {**point, "nx": g(0), "ny": g(0), "nz": g(1)}
    before_x = expectation(ket, world.H).evaluate(point)
    after_x = expectation(evolved_ket, world.H).evaluate(point)
    before_z = expectation(ket, world.H).evaluate(point_z)
    after_z = expectation(evolved_ket, world.H).evaluate(point_z)
    energy_point_ok = (
        before_x == g(0) and after_x == g(0) and before_z == g(1) and after_z == g(1)
    )
    add(
        "Corollario",
        "n = e_x: ⟨H⟩ = 0; n = e_z: ⟨H⟩ = 1, prima e dopo Φ",
        energy_point_ok,
        "c = 3/5, s = 4/5, ψ = |0⟩\n"
        "Universe.Symmetry.point_energy_x, Universe.Symmetry.point_energy_z"
        if energy_point_ok
        else f"x {before_x} → {after_x}; z {before_z} → {after_z}",
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
    lines.append("Collasso della serie, teorema Universe.Qubit.expCoeff_hamiltonian")
    lines.append(f"  {ANALYTIC_PREMISE}")
    return "\n".join(lines)


def main() -> int:
    world = QubitUniverse()
    theorems = prove(world)
    print(render(theorems, world))
    return 0 if all(theorem.holds for theorem in theorems) else 1


def _same_state(left: State, right: State) -> bool:
    return left.dim == right.dim and all(
        a == b for a, b in zip(left.amplitudes, right.amplitudes, strict=True)
    )


def _tensor_associativity() -> tuple[str, bool, str]:
    """Due parentesizzazioni: indici, ampiezze e (U⊗I⊗I) sul primo fattore.

    Gli indici citano `tensor_index` sull'anello `(i, j, k, nb, nc)`.
    Le ampiezze citano `Universe.Composition.tensor_assoc`. L'azione sul
    primo fattore cita `tensor_assoc_ui`. I moduli quadri citano
    `tensor_assoc_obs`.
    """
    name = "(A⊗B)⊗C e A⊗(B⊗C) sono lo stesso stato"
    ring = Ring(("i", "j", "k", "nb", "nc"))
    i, j, k, nb, nc = (ring.var(symbol) for symbol in ring.variables)
    defect = ((i * nb + j) * nc + k) - (i * (nb * nc) + (j * nc + k))
    if not defect.is_zero():
        return name, False, f"resto degli indici = {defect}"
    if not _tensor_layout():
        return name, False, "layout di tensor_state"

    factors = Ring(("u00", "u01", "u10", "u11", "a0", "a1", "b0", "b1", "c0", "c1"))

    def v(symbol: str):
        return factors.var(symbol)

    matrix = Operator.from_rows([[v("u00"), v("u01")], [v("u10"), v("u11")]])
    first = State((v("a0"), v("a1")))
    second = State((v("b0"), v("b1")))
    third = State((v("c0"), v("c1")))
    left = tensor_state(tensor_state(first, second), third)
    right = tensor_state(first, tensor_state(second, third))
    if not _same_state(left, right):
        return name, False, "ampiezze delle due parentesizzazioni"
    if born(left) != born(right):
        return name, False, "moduli quadri delle due parentesizzazioni"

    idle = Operator.eye(factors, 2)
    on_left = matrix.tensor(idle).tensor(idle).apply(left)
    on_right = matrix.tensor(idle.tensor(idle)).apply(right)
    on_blocks = matrix.tensor(Operator.eye(factors, 4)).apply(right)
    evolved = matrix.apply(first)
    factored_left = tensor_state(tensor_state(evolved, second), third)
    factored_right = tensor_state(evolved, tensor_state(second, third))
    phi_ok = (
        _same_state(on_left, factored_left)
        and _same_state(on_right, factored_right)
        and _same_state(on_blocks, factored_right)
        and _same_state(factored_left, factored_right)
        and born(on_left) == born(factored_right)
    )
    if not phi_ok:
        return name, False, "(U⊗I⊗I) sul primo fattore"
    return (
        name,
        True,
        (
            "tensor_index su (i, j, k, nb, nc)\n"
            "ampiezze e (U⊗I⊗I) su (u00, u01, u10, u11, a0, a1, b0, b1, c0, c1)\n"
            "Universe.Composition.tensor_assoc, tensor_assoc_ui, tensor_assoc_obs"
        ),
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


def _free_zero(operator: Operator) -> bool:
    """Ogni entrata ha origine nulla, prima di `reduce`."""
    return all(entry.origin.is_zero() for row in operator.rows for entry in row)


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


def _format_fraction(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def _real_fraction(value: Gauss) -> Fraction:
    if value.im != 0:
        raise ValueError("atteso un peso reale")
    return value.re


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
