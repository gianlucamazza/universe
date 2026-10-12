"""Certificato eseguibile del primo universo. Stampa 77 righe.

Una riga algebrica è dimostrata quando il resto è zero e l'espansione
libera dei cofattori ridà il polinomio. La riga della sezione Tempo non
è un resto: è l'uguaglianza di razionali della legge di addizione, per
ogni grado `m ≤ 12`. Il collasso della serie, nel footer, è
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
`Universe.Observer.order_irrelevant`). Wigner legge l'amico con `cnot12`:
la catena è lo stesso stato del fan-out
(`Universe.Observer.chain_pointers`, `Universe.Observer.chain_is_fanout`,
`Universe.Observer.cnot12_involutive`) e i pesi delle celle 1–6 restano
zero (`Universe.Observer.chain_agree`). Disfare l'amico, `cnot01` due
volte, restituisce `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩` e la coerenza `α β̄`
(`Universe.Observer.friend_undone`,
`Universe.Observer.reduceSystem_product`). Dopo `cnot12` la stessa porta
lascia `α|000⟩ + β|101⟩`: l'antidiagonale del sistema è zero e la
diagonale è il peso di Born (`Universe.Observer.copy_irreversible`).
Il marginale di Wigner resta quel peso
(`Universe.Observer.wigner_keeps_record`). Nel punto `c = 3/5`, `s = 4/5`,
`n = e_x`, con `ψ = Φ|0⟩`, disfare l'amico dà coerenza `12/25 i` e
purezza `1` (`Universe.Observer.point_undone`). Dopo la copia la
coerenza è `0`, la purezza è `337/625` e Wigner legge `9/25` e `16/25`
(`Universe.Observer.point_copied`). Un unitario locale sull'apparato
non cambia i due pesi del sistema. Il conto sta sull'anello
`(c, s, nx, ny, nz, a0r, a0i, a1r, a1i, a2r, a2i, a3r, a3i)`: lo stato è
generico. Lean lo prova per ogni `Quad`,
`Universe.Observer.no_signalling_any_0` e
`Universe.Observer.no_signalling_any_1`, e su `genericQuad`,
`Universe.Observer.no_signalling_gen_0` e
`Universe.Observer.no_signalling_gen_1`. Su tre qubit, sedici reali di
ampiezza più `c`, `s`, `n`, un unitario sul qubit di Wigner e uno sul
qubit dell'amico lasciano i pesi del sistema con resto zero
(`Universe.Observer.no_signalling_wigner`,
`Universe.Observer.no_signalling_friend`).
Una `U` su un qubit qualsiasi di uno stato generico di `n ≤ 4` qubit lascia
la norma con resto zero; Lean lo prova per ogni `n`
(`Universe.Qubits.norm_applyAt`).
Un unitario sul qubit `b` lascia il marginale del qubit `a ≠ b` con resto
zero, per `n = 2, 3, 4` e ogni coppia; Lean lo prova per ogni `n`
(`Universe.Qubits.no_signalling_at`).
Due matrici generiche su qubit diversi commutano sullo stato generico,
per `n = 2, 3, 4`; Lean lo prova per ogni coppia di matrici
(`Universe.Qubits.applyAt_comm`). La traccia parziale su un qubit ha
diagonale uguale al marginale (`Universe.Qubits.reduceAt_diag`). Su un
prodotto è `‖resto‖² |ψ⟩⟨ψ|` (`Universe.Qubits.reduceAt_product`).
Il fan-out di `|ψ⟩ ⊗ |0…0⟩`, un `CNOT` dal sistema verso ogni altro
qubit, è `α|0…0⟩ + β|1…1⟩` (`Universe.Qubits.fanout_ghz`). Ogni coppia
di qubit ha peso zero sulle celle in cui i due bit differiscono
(`Universe.Qubits.fanout_agree`). Per `n ≥ 2` il sistema ridotto è
diagonale con i pesi di Born (`Universe.Qubits.fanout_decoherence`).
Python lo controlla per `n ≤ 5` su un `ψ` generico.
`(n·σ)(m·σ) = (n·m) I + i (n×m)·σ` ha origine zero sull'anello
`(nx, ny, nz, mx, my, mz)`, senza regole (`Universe.Qubit.pauli_product`).
`UH = HU` ha origine libera zero
(`Universe.Symmetry.evolution_commutes_hamiltonian`).
`⟨Uψ|H|Uψ⟩ − ⟨ψ|H|ψ⟩` ha resto zero in `(gC, gN)`
(`Universe.Symmetry.energy_conserved`). Nel punto `c = 3/5`, `s = 4/5`,
`ψ = |0⟩` l'energia vale `0` lungo `e_x` e `1` lungo `e_z`, prima e dopo
`Φ` (`Universe.Symmetry.point_energy_x`, `Universe.Symmetry.point_energy_z`).
`G = |1⟩⟨1| ⊗ H` ha `G³ = G` e `G² = |1⟩⟨1| ⊗ I`
(`Universe.Interaction.generator_cube`, `Universe.Series.expCoeff_idem`).
La forma chiusa è l'evoluzione controllata
(`Universe.Interaction.controlled_from_hamiltonian`). Nel punto
`c = 0`, `s = 1`, `n = e_x` lo stato `|ψ⟩ ⊗ |0⟩` diventa `α|00⟩ − i β|11⟩`
(`Universe.Interaction.cnot_point`, `Universe.Interaction.cnot_point_born`).
Con l'apparato in `|0⟩` la coerenza del sistema ridotto è
`α β̄ · conj(⟨0|U|0⟩)`, con `⟨0|U|0⟩ = c − i s nz`
(`Universe.Interaction.partial_coherence`). La diagonale è il peso di
Born, modulo `(gC, gN)` (`Universe.Interaction.partial_diagonal`).
`ψ` valutato in `3/5`, `−4/5 i` e il coupling lungo `e_x` danno i tre
punti `(1, 0)`, `(3/5, 4/5)` e `(0, 1)`
(`Universe.Interaction.point_partial_idle`,
`Universe.Interaction.point_partial_mid`,
`Universe.Interaction.point_partial_flip`).
Dopo `CNOT` la lettura del puntatore è `(α, 0)` o `(0, β)`, con norme
i pesi di Born (`Universe.Composition.condition`,
`Universe.Interaction.luders`). Un secondo `CNOT` su un apparato fresco
ripete l'esito e azzera l'altro (`Universe.Interaction.repeatable`).
Nel punto `c = 3/5`, `s = 4/5`, `n = e_x` le norme sono `9/25` e `16/25`
(`Universe.Interaction.point_luders`, `Universe.Interaction.point_repeatable`).
La matrice di `U` in quel punto, come `V`, ha `V†V = I` e `VV† = I`
nell'anello libero (`Universe.Symmetry.point_basis_unitary`,
`Universe.Symmetry.point_basis_unitary_rev`). Allora
`V (U ψ) = (V U V†) (V ψ)` (`Universe.Symmetry.conj_evolution`) e
`V (V† φ) = φ` (`Universe.Symmetry.conj_inverse`). I pesi di Born di
`Vψ` nella base `V|k⟩` sono quelli di `ψ` (`Universe.Symmetry.conj_born`).
Nel punto `V(U|0⟩)` vale `−7/25` e `−24/25 i`, con pesi `1` e `0`
(`Universe.Symmetry.point_conj_evolution`, `Universe.Symmetry.point_conj_born`).
`U(c₁, s₁) U(c₂, s₂) − U(c₁c₂ − s₁s₂, s₁c₂ + c₁s₂)` ha resto zero
nell'ideale di `gN` solo, sull'anello fresco `(c1, s1, c2, s2, nx, ny, nz)`
(`Universe.Symmetry.evolution_compose`). Su due assi,
`U(c₁, s₁, n) U(c₂, s₂, m) = a I − i (b·σ)` ha origine zero sull'anello
`(c1, s1, c2, s2, nx, ny, nz, mx, my, mz)`, senza regole
(`Universe.Symmetry.evolution_compose_axes`). Senza quadrati il resto non è zero,
e il quadrato di `c1` da solo non paga la legge. `a² + |b|² − 1` ha resto zero
in `(gC, gN, gC2, gM)` (`Universe.Symmetry.axes_norm_free`,
`Universe.Symmetry.compose_axes_norm`): senza `gM` il resto non è zero, e
`gM` sta fuori da `reduce`, come `gA` e `gC2`. `c² + s² − 1` ha resto zero
con `c1² = 1 − s1²` e la regola extra `c2² = 1 − s2²`
(`Universe.Symmetry.compose_circle`): `gC2` sta fuori da `reduce`, come `gA`.
Nel punto `c₁ = c₂ = 3/5`, `s₁ = s₂ = 4/5`, `n = e_x` l'angolo composto è
`−7/25`, `24/25` e `U|0⟩ = −7/25 |0⟩ − 24/25 i |1⟩`. `evalAt` non legge
`c2` e `s2`. `evalAt2` li legge: `Universe.Symmetry.point_compose`.
Con `m = e_z` lo stesso punto dà `a = 9/25` e
`b = (12/25, −16/25, 12/25)`. `UₙUₘ|0⟩` e `UₘUₙ|0⟩` differiscono
sull'ampiezza di `|1⟩`; i pesi di Born sono `9/25` e `16/25` in entrambi
gli ordini. `evalAt3` legge anche `mx my mz`
(`Universe.Symmetry.point_axes`, `Universe.Symmetry.rotations_noncommute`).
Con `V = U` il resto di `V(Uψ) − (V U V†)(Vψ)` e dei pesi di Born è zero
(`Universe.Symmetry.conj_evolution_law`, `Universe.Symmetry.conj_born_law`).
La sezione Tempo confronta la convoluzione di coseno e seno con il
termine in `x + y`, per `m ≤ 12` e per le frazioni `0`, `±1`, `1/2`,
`3/5`, `−4/5` (`Universe.Angle.angle_add_cos`,
`Universe.Angle.angle_add_sin`).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from universe.angle import addition_scan
from universe.dynamics import evolution, hamiltonian
from universe.epistemology import (
    born,
    computational_projector,
    expectation,
    marginal,
    norm_squared,
)
from universe.interaction import (
    closed_generator,
    coherence_factor,
    condition,
    controlled,
    generator,
    partial_reduced,
    projector_one,
    reread,
)
from universe.observer import (
    cnot,
    cnot01,
    cnot02,
    cnot12,
    determinant_2x2,
    no_signalling_gap,
    no_signalling_three,
    purity,
    reduced,
)
from universe.ontology import Operator, State, determinant, tensor_index, tensor_state
from universe.qubits import (
    embed_qubit,
    fanout,
    generic_state,
    marginal_at,
    on_qubit,
    reduce_at,
)
from universe.ring import ZERO_G, Gauss, Poly, Ring, g
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
    pauli_free = _pauli_product()
    add(
        "Legge",
        "(n·σ)(m·σ) = (n·m) I + i (n×m)·σ nell'anello libero",
        pauli_free,
        "anello (nx, ny, nz, mx, my, mz), senza regole\nUniverse.Qubit.pauli_product"
        if pauli_free
        else "il prodotto di Pauli non è zero nell'anello libero",
    )
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

    qubits_reason = _norm_on_every_qubit(4)
    add(
        "Composizione",
        "U su un qubit qualsiasi di n conserva la norma, n ≤ 4",
        qubits_reason is None,
        "stato generico di n qubit; Lean per ogni n\nUniverse.Qubits.norm_applyAt"
        if qubits_reason is None
        else qubits_reason,
    )

    gates = _gates_commute(4)
    add(
        "Composizione",
        "porte su qubit diversi commutano, n ≤ 4",
        gates is None,
        "matrici generiche, stato generico; Lean per ogni n\n"
        "Universe.Qubits.applyAt_comm"
        if gates is None
        else gates,
    )

    # --- Osservatore: CNOT e il primo stato entangled ---
    gate_ring = Ring(())
    gate = cnot(gate_ring)
    cnot_square = gate.matmul(gate)
    eye4 = Operator.eye(gate_ring, 4)
    add(
        "Osservatore",
        "CNOT² = I",
        cnot_square.rows == eye4.rows,
        "Universe.Observer.cnot_involutive",
    )

    quad_ring = Ring(("a0r", "a0i", "a1r", "a1i", "a2r", "a2i", "a3r", "a3i"))
    generic_quad = State(
        tuple(quad_ring.complex_var(f"a{index}") for index in range(4))
    )
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
        "Universe.Observer.observers_agree_right, "
        "Universe.Observer.order_irrelevant_right"
        if agree_ok
        else "le due porte non coincidono",
    )

    wigner = cnot12(agree_ring)
    chain = wigner.apply(first_observer.apply(prepared_left))
    chain_state_ok = (
        chain.amplitudes == expected_ghz
        and chain.amplitudes == ghz.amplitudes
        and wigner.matmul(wigner).rows == Operator.eye(agree_ring, 8).rows
    )
    add(
        "Osservatore",
        "Wigner, leggendo l'amico, legge il sistema",
        chain_state_ok,
        "α|000⟩ + β|111⟩, come cnot02 ∘ cnot01\n"
        "Universe.Observer.chain_pointers, Universe.Observer.chain_is_fanout,\n"
        "Universe.Observer.cnot12_involutive"
        if chain_state_ok
        else "la catena non è il fan-out",
    )
    chain_weights = born(chain)
    chain_agree_ok = (
        chain_weights[0] == agree_alpha.modulus_squared()
        and chain_weights[7] == agree_beta.modulus_squared()
        and all(weight.is_zero() for weight in chain_weights[1:7])
    )
    add(
        "Osservatore",
        "Wigner e l'amico non sono mai in disaccordo",
        chain_agree_ok,
        "celle 1–6 con peso zero\nUniverse.Observer.chain_agree"
        if chain_agree_ok
        else "i puntatori discordano",
    )

    restored = first_observer.apply(first_observer.apply(prepared_left))
    prepared_system = reduced(prepared_left, 0, 2, 4)
    restored_system = reduced(restored, 0, 2, 4)
    born_alpha = agree_alpha.modulus_squared()
    born_beta = agree_beta.modulus_squared()
    restored_coherence = agree_alpha * agree_beta.conj()
    undone_ok = (
        restored.amplitudes == prepared_left.amplitudes
        and prepared_system.rows[0][0] == born_alpha
        and prepared_system.rows[1][1] == born_beta
        and prepared_system.rows[0][1] == restored_coherence
        and prepared_system.rows[1][0] == agree_beta * agree_alpha.conj()
        and restored_system.rows[0][1] == restored_coherence
    )
    add(
        "Osservatore",
        "disfare l'amico restituisce la coerenza α β̄",
        undone_ok,
        "cnot01 due volte, su |ψ⟩ ⊗ |0⟩ ⊗ |0⟩\n"
        "Universe.Observer.friend_undone, Universe.Observer.reduceSystem_product"
        if undone_ok
        else "la coerenza non torna",
    )

    copied_undone = first_observer.apply(chain)
    irreversible = reduced(copied_undone, 0, 2, 4)
    irreversible_ok = (
        copied_undone.amplitudes
        == (
            agree_alpha,
            agree_zero,
            agree_zero,
            agree_zero,
            agree_zero,
            agree_beta,
            agree_zero,
            agree_zero,
        )
        and irreversible.rows[0][1].is_zero()
        and irreversible.rows[1][0].is_zero()
        and irreversible.rows[0][0] == born_alpha
        and irreversible.rows[1][1] == born_beta
    )
    add(
        "Osservatore",
        "dopo la copia, disfare l'amico lascia il sistema diagonale",
        irreversible_ok,
        "α|000⟩ + β|101⟩, antidiagonale zero\nUniverse.Observer.copy_irreversible"
        if irreversible_ok
        else "la copia non blocca il disfacimento",
    )

    wigner_record = reduced(copied_undone, 1, 4, 2)
    record_ok = (
        wigner_record.rows[0][0] == born_alpha and wigner_record.rows[1][1] == born_beta
    )
    add(
        "Osservatore",
        "Wigner conserva il peso di Born",
        record_ok,
        "marginale del bit basso\nUniverse.Observer.wigner_keeps_record"
        if record_ok
        else "Wigner non legge più il sistema",
    )

    lab = tensor_state(tensor_state(ground, world.ground()), world.ground())
    friend_gate = cnot01(ring)
    wigner_gate = cnot12(ring)
    undone_state = friend_gate.apply(friend_gate.apply(lab))
    copied_state = friend_gate.apply(wigner_gate.apply(friend_gate.apply(lab)))
    undone_rho = reduced(undone_state, 0, 2, 4)
    copied_rho = reduced(copied_state, 0, 2, 4)
    undone_coherence = undone_rho.rows[0][1].evaluate(rational)
    undone_purity = purity(undone_rho).evaluate(rational)
    copied_coherence = copied_rho.rows[0][1].evaluate(rational)
    copied_other = copied_rho.rows[1][0].evaluate(rational)
    copied_purity = purity(copied_rho).evaluate(rational)
    wigner_margin = marginal(copied_state, 1, 4, 2)
    weight0 = wigner_margin[0].evaluate(rational)
    weight1 = wigner_margin[1].evaluate(rational)
    coherence_ok = undone_coherence == g(0, Fraction(12, 25))
    purity_ok = undone_purity == g(1)
    undone_point_ok = coherence_ok and purity_ok
    add(
        "Osservatore",
        "nel punto, disfare l'amico dà coerenza 12/25 i e purezza 1",
        undone_point_ok,
        "ψ = Φ|0⟩, c = 3/5, s = 4/5, n = e_x\nUniverse.Observer.point_undone"
        if undone_point_ok
        else f"coerenza {undone_coherence}, purezza {undone_purity}",
    )
    copied_point_ok = (
        copied_coherence == g(0)
        and copied_other == g(0)
        and copied_purity == g(Fraction(337, 625))
        and weight0 == g(Fraction(9, 25))
        and weight1 == g(Fraction(16, 25))
    )
    add(
        "Osservatore",
        "nel punto, dopo la copia: coerenza 0, purezza 337/625, pesi 9/25 e 16/25",
        copied_point_ok,
        "Wigner legge ancora il sistema\nUniverse.Observer.point_copied"
        if copied_point_ok
        else (
            f"coerenza {copied_coherence}, purezza {copied_purity}, "
            f"pesi {weight0}, {weight1}"
        ),
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

    w0, w1, f0, f1 = no_signalling_three()
    w0_reason, w1_reason = w0.certification(), w1.certification()
    f0_reason, f1_reason = f0.certification(), f1.certification()
    three = "stato generico di tre qubit, anello (c, s, nx, ny, nz, a0r, …, a7i)\n"
    wigner_ok = w0_reason is None and w1_reason is None
    add(
        "Osservatore",
        "un unitario sul qubit di Wigner non cambia i pesi del sistema",
        wigner_ok,
        three + "Universe.Observer.no_signalling_wigner"
        if wigner_ok
        else (w0_reason or w1_reason or ""),
    )
    friend_ok = f0_reason is None and f1_reason is None
    add(
        "Osservatore",
        "un unitario sul qubit dell'amico non cambia i pesi del sistema",
        friend_ok,
        three + "Universe.Observer.no_signalling_friend"
        if friend_ok
        else (f0_reason or f1_reason or ""),
    )

    qubits_signal = _marginal_on_other_qubits(4)
    add(
        "Osservatore",
        "un unitario su un altro qubit non cambia il marginale, n ≤ 4",
        qubits_signal is None,
        "stato generico, n = 2, 3, 4; Lean per ogni n\nUniverse.Qubits.no_signalling_at"
        if qubits_signal is None
        else qubits_signal,
    )

    diagonal = _reduced_diagonal(4)
    add(
        "Osservatore",
        "la diagonale dello stato ridotto è il marginale, n ≤ 4",
        diagonal is None,
        "stato generico, n ≤ 4; Lean per ogni n\nUniverse.Qubits.reduceAt_diag"
        if diagonal is None
        else diagonal,
    )
    on_product = _reduced_on_product(4)
    add(
        "Osservatore",
        "su un prodotto lo stato ridotto è ‖resto‖² |ψ⟩⟨ψ|, n ≤ 4",
        on_product is None,
        "ψ e resto generici, n ≤ 4; Lean per ogni n\nUniverse.Qubits.reduceAt_product"
        if on_product is None
        else on_product,
    )

    copied = _fanout_ghz(5)
    add(
        "Osservatore",
        "il fan-out su |ψ⟩ ⊗ |0…0⟩ è α|0…0⟩ + β|1…1⟩, n ≤ 5",
        copied is None,
        "ψ generico; Lean per ogni n\nUniverse.Qubits.fanout_ghz"
        if copied is None
        else copied,
    )
    agreed = _fanout_agree(5)
    add(
        "Osservatore",
        "nel fan-out ogni coppia di osservatori concorda, n ≤ 5",
        agreed is None,
        "ψ generico, ogni coppia di qubit; Lean per ogni n\n"
        "Universe.Qubits.fanout_agree"
        if agreed is None
        else agreed,
    )
    decohered = _fanout_decoherence(5)
    add(
        "Osservatore",
        "dopo il fan-out il sistema è diagonale con i pesi di Born, n ≤ 5",
        decohered is None,
        "ψ generico, n ≥ 2; Lean per ogni n\nUniverse.Qubits.fanout_decoherence"
        if decohered is None
        else decohered,
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
    point_product = _gauss_matmul(_gauss_dagger(matrix), matrix)
    rational_ok = _is_gauss_identity(point_product)
    add(
        "Corollario",
        "c = 3/5, s = 4/5, n = e_x: U†U = I nei razionali di Gauss",
        rational_ok,
        _format_matrix(matrix) if rational_ok else _format_matrix(point_product),
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

    generated = generator(scalars)
    cube = _power(generated, 3) - generated
    generated_square = generated.matmul(generated) - projector_one(scalars)
    cube_reason = _first_certificate(cube)
    square_reason = _first_certificate(generated_square)
    powers_ok = cube_reason is None and square_reason is None
    add(
        "Interazione",
        "G³ = G e G² = |1⟩⟨1| ⊗ I",
        powers_ok,
        "Universe.Interaction.generator_cube, Universe.Series.expCoeff_idem"
        if powers_ok
        else (cube_reason or square_reason or ""),
    )
    gap = closed_generator(scalars, generated) - controlled(world.U)
    gap_reason = _first_certificate(gap)
    add(
        "Interazione",
        "(1 − G²) + c G² − i s G = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U",
        gap_reason is None,
        "Universe.Interaction.controlled_from_hamiltonian"
        if gap_reason is None
        else gap_reason,
    )
    law = {
        "c": g(0),
        "s": g(1),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    minus_i = ring.constant(g(0, -1))
    alpha = scalars.ar + scalars.ai * ring.constant(g(0, 1))
    beta = scalars.br + scalars.bi * ring.constant(g(0, 1))
    idle = tensor_state(world.generic(), world.ground())
    phased = tuple(
        amplitude.substitute(law)
        for amplitude in controlled(world.U).apply(idle).amplitudes
    )
    expected = (
        alpha.substitute(law),
        ring.zero(),
        ring.zero(),
        (minus_i * beta).substitute(law),
    )
    flipped = cnot(ring).apply(idle)
    born_ok = all(
        left.modulus_squared() == right.substitute(law).modulus_squared()
        for left, right in zip(phased, flipped.amplitudes, strict=True)
    )
    sample = {
        **law,
        "ar": g(Fraction(3, 5)),
        "ai": g(0),
        "br": g(0),
        "bi": g(Fraction(-4, 5)),
    }
    drawn = [amplitude.evaluate(sample) for amplitude in phased]
    phased_weights = [
        _real_fraction(amplitude.modulus_squared().evaluate(sample))
        for amplitude in phased
    ]
    drawn_ok = drawn == [
        g(Fraction(3, 5)),
        g(0),
        g(0),
        g(Fraction(-4, 5)),
    ] and phased_weights == [
        Fraction(9, 25),
        Fraction(0),
        Fraction(0),
        Fraction(16, 25),
    ]
    point_ok = phased == expected and born_ok and drawn_ok
    add(
        "Interazione",
        "nel punto c = 0, s = 1, n = e_x: α|00⟩ − i β|11⟩",
        point_ok,
        "α = 3/5, β = −4/5 i → 3/5|00⟩ − 4/5|11⟩, pesi 9/25 e 16/25\n"
        "Universe.Interaction.cnot_point, Universe.Interaction.cnot_point_born"
        if point_ok
        else f"stato {phased}; pesi {phased_weights}",
    )

    system = world.generic()
    reduced_system = partial_reduced(world.U, system)
    bracket = world.U.rows[0][0]
    bracket_form = scalars.c + ring.constant(g(0, -1)) * scalars.s * scalars.nz
    alpha, beta = system.amplitudes
    factor_ok = (
        reduced_system.rows[0][1] == coherence_factor(world.U, system)
        and reduced_system.rows[1][0] == beta * alpha.conj() * bracket
        and bracket == bracket_form
    )
    add(
        "Interazione",
        "la coerenza parziale è α β̄ · conj(⟨0|U|0⟩)",
        factor_ok,
        "⟨0|U|0⟩ = c − i s nz, anello libero\nUniverse.Interaction.partial_coherence"
        if factor_ok
        else f"⟨0|U|0⟩ = {bracket}",
    )
    born_weights = born(system)
    gap_zero = (reduced_system.rows[0][0] - born_weights[0]).certification()
    gap_one = (reduced_system.rows[1][1] - born_weights[1]).certification()
    diagonal_ok = gap_zero is None and gap_one is None
    add(
        "Interazione",
        "la diagonale parziale è il peso di Born",
        diagonal_ok,
        "modulo (gC, gN), norma di colonna di U\nUniverse.Interaction.partial_diagonal"
        if diagonal_ok
        else (gap_zero or gap_one or ""),
    )
    probe = State(
        (
            ring.constant(g(Fraction(3, 5))),
            ring.constant(g(0, Fraction(-4, 5))),
        )
    )
    probe_rho = partial_reduced(world.U, probe)
    probe_pure = purity(probe_rho)
    axis_x = {"nx": g(1), "ny": g(0), "nz": g(0)}
    expected_points = (
        (Fraction(1), Fraction(0), g(0, Fraction(12, 25)), g(1)),
        (
            Fraction(3, 5),
            Fraction(4, 5),
            g(0, Fraction(36, 125)),
            g(Fraction(11017, 15625)),
        ),
        (Fraction(0), Fraction(1), g(0), g(Fraction(337, 625))),
    )
    point_rows: list[str] = []
    points_hold = True
    for coupling_c, coupling_s, coherence, pure in expected_points:
        sample = {**axis_x, "c": g(coupling_c), "s": g(coupling_s)}
        got_coherence = probe_rho.rows[0][1].evaluate(sample)
        got_purity = probe_pure.evaluate(sample)
        points_hold = points_hold and got_coherence == coherence and got_purity == pure
        point_rows.append(
            f"({coupling_c}, {coupling_s}): {got_coherence}, purezza {got_purity}"
        )
    add(
        "Interazione",
        "tre punti della misura parziale, lungo e_x",
        points_hold,
        "α = 3/5, β = −4/5 i\n"
        "(1, 0): 12/25 i, purezza 1\n"
        "(3/5, 4/5): 36/125 i, purezza 11017/15625\n"
        "(0, 1): 0, purezza 337/625\n"
        "Universe.Interaction.point_partial_idle, "
        "Universe.Interaction.point_partial_mid,\n"
        "Universe.Interaction.point_partial_flip"
        if points_hold
        else "\n".join(point_rows),
    )

    system = world.generic()
    zero = system.ring.zero()
    alpha, beta = system.amplitudes
    coupled = cnot(system.ring).apply(tensor_state(system, world.ground()))
    read0 = condition(coupled, 0)
    read1 = condition(coupled, 1)
    born_weights = born(system)
    luders_ok = (
        read0.amplitudes == (alpha, zero)
        and read1.amplitudes == (zero, beta)
        and norm_squared(read0) == born_weights[0]
        and norm_squared(read1) == born_weights[1]
    )
    add(
        "Interazione",
        "dopo CNOT, la lettura 0 è (α, 0) e la lettura 1 è (0, β)",
        luders_ok,
        "le norme sono i pesi di Born, anello libero\n"
        "Universe.Composition.condition, Universe.Interaction.luders"
        if luders_ok
        else f"0 = {read0.amplitudes}; 1 = {read1.amplitudes}",
    )
    second0 = marginal(reread(system, 0), 1, 2, 2)
    second1 = marginal(reread(system, 1), 1, 2, 2)
    repeat_ok = (
        second0[0] == norm_squared(read0)
        and second0[1] == zero
        and second1[1] == norm_squared(read1)
        and second1[0] == zero
    )
    add(
        "Interazione",
        "una seconda lettura ripete l'esito e azzera l'altro",
        repeat_ok,
        "il peso è la norma dello stato condizionato\nUniverse.Interaction.repeatable"
        if repeat_ok
        else f"0 → {second0}; 1 → {second1}",
    )
    evolved_ground = world.evolve(world.ground())
    sample = {
        "c": g(Fraction(3, 5)),
        "s": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    pointed = cnot(evolved_ground.ring).apply(
        tensor_state(evolved_ground, world.ground())
    )
    pointed0 = condition(pointed, 0)
    pointed1 = condition(pointed, 1)
    got0 = tuple(amplitude.evaluate(sample) for amplitude in pointed0.amplitudes)
    got1 = tuple(amplitude.evaluate(sample) for amplitude in pointed1.amplitudes)
    norm0 = norm_squared(pointed0).evaluate(sample)
    norm1 = norm_squared(pointed1).evaluate(sample)
    point_luders_ok = (
        got0 == (g(Fraction(3, 5)), g(0))
        and got1 == (g(0), g(0, Fraction(-4, 5)))
        and norm0 == g(Fraction(9, 25))
        and norm1 == g(Fraction(16, 25))
    )
    add(
        "Interazione",
        "nel punto, lo stato condizionato è 3/5|0⟩ e −4/5 i|1⟩",
        point_luders_ok,
        "norme 9/25 e 16/25\nUniverse.Interaction.point_luders"
        if point_luders_ok
        else f"0 = {got0}, norma {norm0}; 1 = {got1}, norma {norm1}",
    )
    again0 = marginal(reread(evolved_ground, 0), 1, 2, 2)
    again1 = marginal(reread(evolved_ground, 1), 1, 2, 2)
    point_repeat_ok = (
        again0[0].evaluate(sample) == g(Fraction(9, 25))
        and again0[1].evaluate(sample) == g(0)
        and again1[0].evaluate(sample) == g(0)
        and again1[1].evaluate(sample) == g(Fraction(16, 25))
    )
    add(
        "Interazione",
        "nel punto, la seconda lettura ripete 9/25 e 16/25",
        point_repeat_ok,
        "l'altro esito pesa 0\nUniverse.Interaction.point_repeatable"
        if point_repeat_ok
        else f"0 → ({again0[0].evaluate(sample)}, {again0[1].evaluate(sample)}); "
        f"1 → ({again1[0].evaluate(sample)}, {again1[1].evaluate(sample)})",
    )

    change = _change_of_basis(world)
    add(
        "Simmetria",
        "V(Uψ) = (V U V†)(Vψ) nell'anello libero",
        change.evolution,
        "V†V = I e VV† = I, V = U(3/5, 4/5, e_x)\n"
        "Universe.Symmetry.conj_evolution, Universe.Symmetry.conj_inverse"
        if change.evolution
        else "il cambio di base non coincide",
    )
    add(
        "Simmetria",
        "i pesi di Born di Vψ nella base V|k⟩ sono quelli di ψ",
        change.born,
        "anello libero, stato generico\nUniverse.Symmetry.conj_born"
        if change.born
        else "i pesi non coincidono",
    )
    conj_drawn = change.image == (
        g(Fraction(-7, 25)),
        g(0, Fraction(-24, 25)),
    ) and change.weights == (g(1), g(0))
    add(
        "Simmetria",
        "nel punto, V(U|0⟩) = −7/25 |0⟩ − 24/25 i |1⟩, pesi 1 e 0",
        conj_drawn and change.evolution,
        "c = 3/5, s = 4/5, n = e_x, ψ = |0⟩\n"
        "Universe.Symmetry.point_conj_evolution, Universe.Symmetry.point_conj_born"
        if conj_drawn and change.evolution
        else f"stato {_format_gauss(change.image[0])}, "
        f"{_format_gauss(change.image[1])}; "
        f"pesi {_format_gauss(change.weights[0])}, {_format_gauss(change.weights[1])}",
    )

    symbolic = _symbolic_conjugation(world)
    add(
        "Simmetria",
        "V(Uψ) − (V U V†)(Vψ) sta in (gC, gN), con V = U",
        symbolic.evolution,
        "resto zero sulle ampiezze, stato generico\n"
        "Universe.Symmetry.conj_evolution_rel, Universe.Symmetry.conj_evolution_law"
        if symbolic.evolution
        else "il trasporto simbolico non sta in (gC, gN)",
    )
    add(
        "Simmetria",
        "i pesi di Born di Vψ nella base V|k⟩ e quelli di ψ stanno in (gC, gN)",
        symbolic.born,
        "V = U, stato generico\n"
        "Universe.Symmetry.conj_born_rel, Universe.Symmetry.conj_born_law"
        if symbolic.born
        else "i pesi simbolici non stanno in (gC, gN)",
    )

    time_law = _time_composition()
    add(
        "Simmetria",
        "U(c₁, s₁) U(c₂, s₂) − U(c, s) sta nell'ideale di gN",
        time_law.group,
        "solo nx² = 1 − ny² − nz²; senza quadrati il resto non è zero\n"
        "Universe.Symmetry.evolution_compose"
        if time_law.group
        else "la legge di gruppo non sta in (gN)",
    )
    axes_gap = _axes_composition(Ring((*_LAW, "mx", "my", "mz")))
    axes_free = _free_zero(axes_gap) and _first_certificate(axes_gap) is None
    add(
        "Simmetria",
        "U(c₁, s₁, n) U(c₂, s₂, m) = a I − i (b·σ) nell'anello libero",
        axes_free,
        "anello (c1, s1, c2, s2, nx, ny, nz, mx, my, mz), senza regole\n"
        "Universe.Symmetry.evolution_compose_axes"
        if axes_free
        else "il prodotto su due assi non è zero nell'anello libero",
    )
    axes_norm = _axes_norm()
    add(
        "Simmetria",
        "a² + |b|² − 1 sta in (gC, gN, gC2, gM)",
        axes_norm,
        "senza gM il resto non è zero; gM fuori da reduce, come gA e gC2\n"
        "Universe.Symmetry.axes_norm_free, Universe.Symmetry.compose_axes_norm"
        if axes_norm
        else "la norma del prodotto non sta in (gC, gN, gC2, gM)",
    )
    axes_drawn = _axes_point()
    forward_image = (
        g(Fraction(9, 25), Fraction(-12, 25)),
        g(Fraction(-16, 25), Fraction(-12, 25)),
    )
    backward_image = (
        g(Fraction(9, 25), Fraction(-12, 25)),
        g(Fraction(16, 25), Fraction(-12, 25)),
    )
    axes_weights = (g(Fraction(9, 25)), g(Fraction(16, 25)))
    point_axes_ok = (
        axes_drawn.amplitude == g(Fraction(9, 25))
        and axes_drawn.vector
        == (
            g(Fraction(12, 25)),
            g(Fraction(-16, 25)),
            g(Fraction(12, 25)),
        )
        and axes_drawn.forward == forward_image
    )
    add(
        "Simmetria",
        "nel punto, a = 9/25, b = (12/25, −16/25, 12/25) e "
        "UₙUₘ|0⟩ = (9/25 − 12/25 i)|0⟩ + (−16/25 − 12/25 i)|1⟩",
        point_axes_ok,
        "c₁ = c₂ = 3/5, s₁ = s₂ = 4/5, n = e_x, m = e_z; "
        "evalAt3 legge anche mx my mz\n"
        "Universe.Symmetry.point_axes"
        if point_axes_ok
        else "a {}, b {}; stato {}, {}".format(
            _format_gauss(axes_drawn.amplitude),
            ", ".join(_format_gauss(part) for part in axes_drawn.vector),
            _format_gauss(axes_drawn.forward[0]),
            _format_gauss(axes_drawn.forward[1]),
        ),
    )
    orders_ok = (
        axes_drawn.backward == backward_image
        and axes_drawn.forward[1] != axes_drawn.backward[1]
        and axes_drawn.forward_weights == axes_weights
        and axes_drawn.backward_weights == axes_weights
    )
    add(
        "Simmetria",
        "UₙUₘ|0⟩ e UₘUₙ|0⟩ differiscono su |1⟩, con pesi 9/25 e 16/25",
        orders_ok,
        "lo stesso punto: |1⟩ vale −16/25 − 12/25 i e 16/25 − 12/25 i\n"
        "Universe.Symmetry.rotations_noncommute"
        if orders_ok
        else "ordini {}, {} e {}, {}; pesi {}, {} e {}, {}".format(
            *map(
                _format_gauss,
                axes_drawn.forward
                + axes_drawn.backward
                + axes_drawn.forward_weights
                + axes_drawn.backward_weights,
            )
        ),
    )
    add(
        "Simmetria",
        "se le due coppie stanno sul cerchio, ci sta (c, s)",
        time_law.circle,
        "gC2 fuori da reduce, come gA: regola extra c2² = 1 − s2²\n"
        "Universe.Symmetry.compose_circle"
        if time_law.circle
        else "il composto non sta in (gC, gC2)",
    )
    point_ok = time_law.angle == (
        g(Fraction(-7, 25)),
        g(Fraction(24, 25)),
    ) and time_law.image == (
        g(Fraction(-7, 25)),
        g(0, Fraction(-24, 25)),
    )
    add(
        "Simmetria",
        "nel punto, U|0⟩ = −7/25 |0⟩ − 24/25 i |1⟩ con c = −7/25, s = 24/25",
        point_ok,
        "c₁ = c₂ = 3/5, s₁ = s₂ = 4/5, n = e_x; evalAt2 legge anche c2 e s2\n"
        "Universe.Symmetry.evolution_compose, Universe.Symmetry.compose_circle, "
        "Universe.Symmetry.point_compose"
        if point_ok
        else "angolo {}, {}; stato {}, {}".format(
            *map(_format_gauss, time_law.angle + time_law.image)
        ),
    )
    holds, detail = addition_scan()
    cited = "Universe.Angle.angle_add_cos, Universe.Angle.angle_add_sin"
    add(
        "Tempo",
        "la legge di addizione di coseno e seno, a ogni grado",
        holds,
        f"{detail}\n{cited}" if holds else detail,
    )
    return proven


@dataclass(frozen=True)
class _BasisChange:
    evolution: bool
    born: bool
    image: tuple[Gauss, Gauss]
    weights: tuple[Gauss, Gauss]


def _origin_zero(left: Poly, right: Poly) -> bool:
    return (left - right).origin.is_zero()


def _gap_zero(left: Poly, right: Poly) -> bool:
    return (left - right).certification() is None


@dataclass(frozen=True)
class _SymbolicBasis:
    evolution: bool
    born: bool


def _symbolic_conjugation(world: QubitUniverse) -> _SymbolicBasis:
    """`V = U` sul quoziente: il resto di `V(Uψ) − (VUV†)(Vψ)` è zero.

    I pesi di Born di `Vψ` nella base `V|k⟩` hanno lo stesso resto.
    """
    basis = world.U
    state = world.generic()
    transported = basis.apply(world.U.apply(state))
    conjugated = basis.matmul(world.U).matmul(basis.dagger())
    pulled = conjugated.apply(basis.apply(state))
    evolution_ok = all(
        _gap_zero(left, right)
        for left, right in zip(transported.amplitudes, pulled.amplitudes, strict=True)
    )
    ring = state.ring
    ket0 = State((ring.one(), ring.zero()))
    ket1 = State((ring.zero(), ring.one()))
    image = basis.apply(state)

    def bracket(bra: State, ket: State) -> Poly:
        total = ring.zero()
        for left, right in zip(bra.amplitudes, ket.amplitudes, strict=True):
            total = total + left.conj() * right
        return total

    weights = tuple(
        bracket(basis.apply(ket), image).modulus_squared() for ket in (ket0, ket1)
    )
    born_ok = all(
        _gap_zero(weight, amplitude.modulus_squared())
        for weight, amplitude in zip(weights, state.amplitudes, strict=True)
    )
    return _SymbolicBasis(evolution_ok, born_ok)


def _change_of_basis(world: QubitUniverse) -> _BasisChange:
    """`V` è `U` nel punto `c = 3/5`, `s = 4/5`, `n = e_x`, a entrate costanti.

    L'uguaglianza è sull'origine libera, prima di `reduce`.
    """
    ring = world.scalars.ring
    real = ring.constant(g(Fraction(3, 5)))
    imag = ring.constant(g(0, Fraction(-4, 5)))
    basis = Operator.from_rows([[real, imag], [imag, real]])
    eye = Operator.eye(ring, 2)
    left_unitary = basis.dagger().matmul(basis)
    right_unitary = basis.matmul(basis.dagger())
    unitary = all(
        _origin_zero(entry, target)
        for operator in (left_unitary, right_unitary)
        for row, goal in zip(operator.rows, eye.rows, strict=True)
        for entry, target in zip(row, goal, strict=True)
    )
    state = world.generic()
    conjugated = basis.matmul(world.U).matmul(basis.dagger())
    transported = basis.apply(world.U.apply(state))
    pulled = conjugated.apply(basis.apply(state))
    evolution_same = unitary and all(
        _origin_zero(left, right)
        for left, right in zip(transported.amplitudes, pulled.amplitudes, strict=True)
    )
    ket0 = State((ring.one(), ring.zero()))
    ket1 = State((ring.zero(), ring.one()))
    image = basis.apply(state)

    def bracket(bra: State, ket: State):
        total = ring.zero()
        for left, right in zip(bra.amplitudes, ket.amplitudes, strict=True):
            total = total + left.conj() * right
        return total

    weights = tuple(
        bracket(basis.apply(ket), image).modulus_squared() for ket in (ket0, ket1)
    )
    born = all(
        _origin_zero(weight, amplitude.modulus_squared())
        for weight, amplitude in zip(weights, state.amplitudes, strict=True)
    )
    axis = {
        "c": g(Fraction(3, 5)),
        "s": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    ground = basis.apply(world.U.apply(world.ground()))
    conjugated_ground = conjugated.apply(basis.apply(world.ground()))
    same_point = all(
        _origin_zero(left, right)
        for left, right in zip(
            ground.amplitudes, conjugated_ground.amplitudes, strict=True
        )
    )
    image0, image1 = (amplitude.evaluate(axis) for amplitude in ground.amplitudes)
    weight0, weight1 = (
        bracket(basis.apply(ket), basis.apply(world.ground()))
        .modulus_squared()
        .evaluate(axis)
        for ket in (ket0, ket1)
    )
    return _BasisChange(
        evolution_same and same_point,
        born,
        (image0, image1),
        (weight0, weight1),
    )


_LAW = ("c1", "s1", "c2", "s2", "nx", "ny", "nz")


@dataclass(frozen=True)
class _TimeLaw:
    group: bool
    circle: bool
    angle: tuple[Gauss, Gauss]
    image: tuple[Gauss, Gauss]


def _gate_names() -> tuple[str, ...]:
    """Otto reali per ciascuna di due matrici `2×2`."""
    return tuple(
        f"{prefix}{row}{col}{part}"
        for prefix in ("u", "v")
        for row in range(2)
        for col in range(2)
        for part in ("r", "i")
    )


def _matrix(ring: Ring, prefix: str) -> Operator:
    """Matrice `2×2` con entrate `prefix{r}{c}r + i prefix{r}{c}i`."""
    return Operator.from_rows(
        [
            [ring.complex_var(f"{prefix}{row}{col}") for col in range(2)]
            for row in range(2)
        ]
    )


def _gates_commute(max_n: int) -> str | None:
    """Due matrici su qubit diversi, nei due ordini, danno lo stesso stato."""
    for n in range(2, max_n + 1):
        law, state = generic_state(n, _gate_names())
        left, right = _matrix(law.ring, "u"), _matrix(law.ring, "v")
        for source in range(n):
            for target in range(n):
                if source == target:
                    continue
                forward = on_qubit(left, source, n).apply(
                    on_qubit(right, target, n).apply(state)
                )
                backward = on_qubit(right, target, n).apply(
                    on_qubit(left, source, n).apply(state)
                )
                if forward.amplitudes != backward.amplitudes:
                    return f"n = {n}, a = {source}, b = {target}"
    return None


def _reduced_diagonal(max_n: int) -> str | None:
    """La diagonale di `reduce_at` è `marginal_at`."""
    for n in range(1, max_n + 1):
        _, state = generic_state(n)
        for qubit in range(n):
            rho = reduce_at(state, qubit)
            p0, p1 = marginal_at(state, qubit)
            if rho.rows[0][0] != p0 or rho.rows[1][1] != p1:
                return f"n = {n}, qubit {qubit}"
    return None


def _reduced_on_product(max_n: int) -> str | None:
    """`reduce_at` di `|ψ⟩` sul qubit `k` è `‖resto‖² |ψ⟩⟨ψ|`."""
    for n in range(1, max_n + 1):
        rest_dim = 1 << (n - 1)
        names = tuple(f"p{bit}{part}" for bit in range(2) for part in ("r", "i"))
        names += tuple(f"b{k}{part}" for k in range(rest_dim) for part in ("r", "i"))
        ring = Ring(names)
        psi = State(tuple(ring.complex_var(f"p{bit}") for bit in range(2)))
        rest = tuple(ring.complex_var(f"b{k}") for k in range(rest_dim))
        weight = norm_squared(State(rest))
        alpha, beta = psi.amplitudes
        pure = Operator.from_rows(
            [
                [alpha.modulus_squared(), alpha * beta.conj()],
                [beta * alpha.conj(), beta.modulus_squared()],
            ]
        ).scale(weight)
        for qubit in range(n):
            rho = reduce_at(embed_qubit(psi, rest, qubit), qubit)
            if rho.rows != pure.rows:
                return f"n = {n}, qubit {qubit}"
    return None


def _marginal_on_other_qubits(max_n: int) -> str | None:
    """Il marginale del qubit `a` dopo `U` sul qubit `b ≠ a`, resto zero."""
    for n in range(2, max_n + 1):
        law, state = generic_state(n)
        gate = evolution(law, hamiltonian(law))
        before = [marginal_at(state, qubit) for qubit in range(n)]
        for source in range(n):
            moved = on_qubit(gate, source, n).apply(state)
            for target in range(n):
                if target == source:
                    continue
                after = marginal_at(moved, target)
                gaps = (after[0] - before[target][0], after[1] - before[target][1])
                for component, gap in enumerate(gaps):
                    reason = gap.certification()
                    if reason is not None:
                        return (
                            f"n = {n}, a = {target}, b = {source}, "
                            f"P({component}): {reason}"
                        )
    return None


def _fanout_ghz(max_n: int) -> str | None:
    """Il fan-out è `α|0…0⟩ + β|1…1⟩`. Le altre ampiezze sono zero."""
    for n in range(1, max_n + 1):
        _, psi = generic_state(1)
        alpha, beta = psi.amplitudes
        state = fanout(psi, n)
        if state.amplitudes[0] != alpha or state.amplitudes[-1] != beta:
            return f"n = {n}: le ampiezze estreme"
        if any(not amplitude.is_zero() for amplitude in state.amplitudes[1:-1]):
            return f"n = {n}: una foglia interna"
    return None


def _fanout_agree(max_n: int) -> str | None:
    """Ogni coppia di qubit: le celle in cui differiscono hanno peso zero."""
    for n in range(2, max_n + 1):
        _, psi = generic_state(1)
        weights = born(fanout(psi, n))
        for left in range(n):
            for right in range(left + 1, n):
                for index, weight in enumerate(weights):
                    bit_left = (index >> (n - 1 - left)) & 1
                    bit_right = (index >> (n - 1 - right)) & 1
                    if bit_left != bit_right and not weight.is_zero():
                        return f"n = {n}, qubit {left} e {right}, cella {index}"
    return None


def _fanout_decoherence(max_n: int) -> str | None:
    """Per `n ≥ 2` il sistema ridotto è diagonale, con i pesi di Born di `ψ`."""
    for n in range(2, max_n + 1):
        _, psi = generic_state(1)
        weights = born(psi)
        rho = reduce_at(fanout(psi, n), 0)
        if (
            not rho.rows[0][1].is_zero()
            or not rho.rows[1][0].is_zero()
            or rho.rows[0][0] != weights[0]
            or rho.rows[1][1] != weights[1]
        ):
            return f"n = {n}"
    return None


def _norm_on_every_qubit(max_n: int) -> str | None:
    """`‖U_k v‖² − ‖v‖²` in `(gC, gN)` per ogni `n ≤ max_n` e ogni qubit `k`."""
    for n in range(1, max_n + 1):
        law, state = generic_state(n)
        gate = evolution(law, hamiltonian(law))
        before = norm_squared(state)
        for qubit in range(n):
            gap = norm_squared(on_qubit(gate, qubit, n).apply(state)) - before
            reason = gap.certification()
            if reason is not None:
                return f"n = {n}, qubit {qubit}: {reason}"
    return None


def _pauli_product() -> bool:
    """`(n·σ)(m·σ) = (n·m) I + i (n×m)·σ` nell'anello libero, senza regole."""
    ring = Ring(("nx", "ny", "nz", "mx", "my", "mz"))
    nx, ny, nz, mx, my, mz = (ring.var(name) for name in ring.variables)
    product = _axis_hamiltonian(ring, nx, ny, nz).matmul(
        _axis_hamiltonian(ring, mx, my, mz)
    )
    dot = nx * mx + ny * my + nz * mz
    crossed = _axis_hamiltonian(
        ring,
        ny * mz - nz * my,
        nz * mx - nx * mz,
        nx * my - ny * mx,
    )
    imag = ring.constant(g(0, 1))
    closed = Operator.eye(ring, 2).scale(dot) + crossed.scale(imag)
    gap = product - closed
    return _free_zero(gap) and _first_certificate(gap) is None


def _axis_hamiltonian(ring: Ring, nx: Poly, ny: Poly, nz: Poly) -> Operator:
    """`n · σ` su un anello qualsiasi, con `Y = [[0, −i], [i, 0]]`."""
    zero, one = ring.zero(), ring.one()
    imag = ring.constant(g(0, 1))
    minus = ring.constant(g(0, -1))
    sigma_x = Operator.from_rows([[zero, one], [one, zero]])
    sigma_y = Operator.from_rows([[zero, minus], [imag, zero]])
    sigma_z = Operator.from_rows([[one, zero], [zero, -one]])
    return sigma_x.scale(nx) + sigma_y.scale(ny) + sigma_z.scale(nz)


def _evolution_cs(cosine: Poly, sine: Poly, generator: Operator) -> Operator:
    """`c I − i s H`."""
    eye = Operator.eye(cosine.ring, generator.n)
    minus = cosine.ring.constant(g(0, -1))
    return eye.scale(cosine) + generator.scale(minus * sine)


def _composition(ring: Ring) -> tuple[Operator, Poly, Poly, Operator]:
    symbol = {name: ring.var(name) for name in _LAW}
    generator = _axis_hamiltonian(ring, symbol["nx"], symbol["ny"], symbol["nz"])
    first = _evolution_cs(symbol["c1"], symbol["s1"], generator)
    second = _evolution_cs(symbol["c2"], symbol["s2"], generator)
    cosine = symbol["c1"] * symbol["c2"] - symbol["s1"] * symbol["s2"]
    sine = symbol["s1"] * symbol["c2"] + symbol["c1"] * symbol["s2"]
    closed = _evolution_cs(cosine, sine, generator)
    return first.matmul(second) - closed, cosine, sine, closed


def _axes_pair(ring: Ring) -> tuple[Poly, Poly, Poly, Poly]:
    """`a` e le tre componenti di `b`, come in `evolution_compose_axes`."""
    c1, s1, c2, s2, nx, ny, nz, mx, my, mz = (
        ring.var(name) for name in (*_LAW, "mx", "my", "mz")
    )
    dotted = nx * mx + ny * my + nz * mz
    return (
        c1 * c2 - s1 * s2 * dotted,
        s1 * c2 * nx + c1 * s2 * mx + s1 * s2 * (ny * mz - nz * my),
        s1 * c2 * ny + c1 * s2 * my + s1 * s2 * (nz * mx - nx * mz),
        s1 * c2 * nz + c1 * s2 * mz + s1 * s2 * (nx * my - ny * mx),
    )


def _axes_factors(ring: Ring) -> tuple[Operator, Operator]:
    """`U(c₁, s₁, n)` e `U(c₂, s₂, m)`, gli stessi fattori di `_axes_composition`."""
    c1, s1, c2, s2, nx, ny, nz, mx, my, mz = (
        ring.var(name) for name in (*_LAW, "mx", "my", "mz")
    )
    first = _evolution_cs(c1, s1, _axis_hamiltonian(ring, nx, ny, nz))
    second = _evolution_cs(c2, s2, _axis_hamiltonian(ring, mx, my, mz))
    return first, second


def _axes_composition(ring: Ring) -> Operator:
    """`U(c₁, s₁, n) U(c₂, s₂, m) − (a I − i (b·σ))`, su `_LAW` più `mx my mz`."""
    first, second = _axes_factors(ring)
    amplitude, bx, by, bz = _axes_pair(ring)
    closed = _evolution_cs(amplitude, ring.one(), _axis_hamiltonian(ring, bx, by, bz))
    return first.matmul(second) - closed


@dataclass(frozen=True)
class _AxesPoint:
    amplitude: Gauss
    vector: tuple[Gauss, Gauss, Gauss]
    forward: tuple[Gauss, Gauss]
    backward: tuple[Gauss, Gauss]
    forward_weights: tuple[Gauss, Gauss]
    backward_weights: tuple[Gauss, Gauss]


def _axes_point() -> _AxesPoint:
    """Il punto `n = e_x`, `m = e_z`, `c₁ = c₂ = 3/5`, `s₁ = s₂ = 4/5`.

    `a` e `b` vengono da `_axes_pair`. I due ordini sono i fattori di
    `_axes_composition`, applicati a `|0⟩`.
    """
    ring = Ring((*_LAW, "mx", "my", "mz"))
    amplitude, bx, by, bz = _axes_pair(ring)
    first, second = _axes_factors(ring)
    ket = State((ring.one(), ring.zero()))
    forward = first.matmul(second).apply(ket)
    backward = second.matmul(first).apply(ket)
    point = {
        "c1": g(Fraction(3, 5)),
        "s1": g(Fraction(4, 5)),
        "c2": g(Fraction(3, 5)),
        "s2": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
        "mx": g(0),
        "my": g(0),
        "mz": g(1),
    }

    def image(state: State) -> tuple[Gauss, Gauss]:
        return (
            state.amplitudes[0].evaluate(point),
            state.amplitudes[1].evaluate(point),
        )

    def weights(state: State) -> tuple[Gauss, Gauss]:
        return (
            state.amplitudes[0].modulus_squared().evaluate(point),
            state.amplitudes[1].modulus_squared().evaluate(point),
        )

    return _AxesPoint(
        amplitude.evaluate(point),
        (bx.evaluate(point), by.evaluate(point), bz.evaluate(point)),
        image(forward),
        image(backward),
        weights(forward),
        weights(backward),
    )


def _axes_norm() -> bool:
    """`a² + |b|² − 1` in `(gC, gN, gC2, gM)`. Senza `gM` il resto non è zero.

    `set_square` sbuccia `c1` e `nx`. `c2` e `mx` entrano con `certify_extras`:
    `gC2` e `gM` restano fuori da `reduce`, come `gA`.
    """
    ring = Ring((*_LAW, "mx", "my", "mz"))
    ring.set_square("c1", ring.one() - ring.var("s1") ** 2)
    ring.set_square("nx", ring.one() - ring.var("ny") ** 2 - ring.var("nz") ** 2)
    amplitude, bx, by, bz = _axes_pair(ring)
    gap = amplitude**2 + bx**2 + by**2 + bz**2 - ring.one()
    circle = ("c2", ring.one() - ring.var("s2") ** 2)
    axis = ("mx", ring.one() - ring.var("my") ** 2 - ring.var("mz") ** 2)
    return (
        gap.certify_extras((circle,)) is not None
        and gap.certify_extras((circle, axis)) is None
    )


def _certified(operator: Operator) -> bool:
    return all(entry.certification() is None for row in operator.rows for entry in row)


def _time_composition() -> _TimeLaw:
    """Legge di gruppo in `(gN)` e cerchio in `(gC, gC2)`, su anelli freschi.

    `set_square` sbuccia solo `nx`, poi solo `c1`. `c2` entra con `certify_extra`,
    come `gA`: `reduce` non lo sbuccia.
    """
    axis = Ring(_LAW)
    one = axis.one()
    axis.set_square("nx", one - axis.var("ny") ** 2 - axis.var("nz") ** 2)
    on_axis = _certified(_composition(axis)[0])
    not_free = not _certified(_composition(Ring(_LAW))[0])
    circle_ring = Ring(_LAW)
    circle_ring.set_square("c1", circle_ring.one() - circle_ring.var("s1") ** 2)
    circle_misses = not _certified(_composition(circle_ring)[0])

    sphere = Ring(_LAW)
    sphere.set_square("c1", sphere.one() - sphere.var("s1") ** 2)
    _, cosine, sine, _closed = _composition(sphere)
    gap = cosine**2 + sine**2 - sphere.one()
    needs_extra = gap.certification() is not None
    paid = gap.certify_extra("c2", sphere.one() - sphere.var("s2") ** 2) is None

    point_ring = Ring(_LAW)
    _, cosine, sine, closed = _composition(point_ring)
    point = {
        "c1": g(Fraction(3, 5)),
        "s1": g(Fraction(4, 5)),
        "c2": g(Fraction(3, 5)),
        "s2": g(Fraction(4, 5)),
        "nx": g(1),
        "ny": g(0),
        "nz": g(0),
    }
    evolved = closed.apply(State((point_ring.one(), point_ring.zero())))
    return _TimeLaw(
        group=on_axis and not_free and circle_misses,
        circle=needs_extra and paid,
        angle=(cosine.evaluate(point), sine.evaluate(point)),
        image=(
            evolved.amplitudes[0].evaluate(point),
            evolved.amplitudes[1].evaluate(point),
        ),
    )


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
    lines.append(f"{passed}/{len(theorems)} righe dimostrate.")
    lines.append("")
    lines.append("Collasso della serie, teorema Universe.Qubit.expCoeff_hamiltonian")
    lines.append(f"  {ANALYTIC_PREMISE}")
    lines.append(
        "Se a³ = a, i coefficienti sono quelli di (1 − a²) + cos φ · a² − i sin φ · a"
    )
    lines.append("  (Universe.Series.expCoeff_idem).")
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
