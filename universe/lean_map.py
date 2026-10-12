"""Lean theorems behind each line of the certificate.

Every line printed by `python -m universe` names at least one Lean theorem.
`tests/test_lean_map.py` checks that the keys are exactly the certificate
lines and that every name is declared in `Universe/`.
"""

LEAN: dict[str, tuple[str, ...]] = {
    "(1+i)(1−i) = 2": ("Universe.Ring.Gauss.one_add_i_mul_one_sub_i",),
    "c² + s² − 1 ≡ 0": (
        "Universe.Dynamics.inIdeal_gC",
        "Universe.Quotient.reduce_sound",
        "Universe.Dynamics.reduce_complete",
    ),
    "nx² + ny² + nz² − 1 ≡ 0": (
        "Universe.Dynamics.inIdeal_gN",
        "Universe.Quotient.reduce_sound",
        "Universe.Dynamics.reduce_complete",
    ),
    "H† = H": ("Universe.Qubit.hamiltonian_dagger",),
    "H² = I": ("Universe.Qubit.hamiltonian_sq",),
    "H³ = H": ("Universe.Qubit.hamiltonian_cube",),
    "H⁴ = I": ("Universe.Qubit.hamiltonian_fourth",),
    "(n·σ)(m·σ) = (n·m) I + i (n×m)·σ nell'anello libero": (
        "Universe.Qubit.pauli_product",
    ),
    "U†U = I": ("Universe.Qubit.evolution_unitary",),
    "UU† = I": ("Universe.Qubit.evolution_unitary_rev",),
    "det U = 1": ("Universe.Qubit.evolution_det",),
    "‖Uψ‖² = ‖ψ‖² per ogni ampiezza": (
        "Universe.Epistemology.literal_evolution_norm",
        "Universe.Qubit.evolution_norm",
    ),
    "UH = HU nell'anello libero": ("Universe.Symmetry.evolution_commutes_hamiltonian",),
    "⟨Uψ|H|Uψ⟩ = ⟨ψ|H|ψ⟩": ("Universe.Symmetry.energy_conserved",),
    "P(0) + P(1) = 1 sullo stato fondamentale evoluto": (
        "Universe.Epistemology.ground_prob_sum",
    ),
    "sulla sfera unitaria, P(0) + P(1) = 1": (
        "Universe.Epistemology.sphere_prob_sum",
        "Universe.Epistemology.literal_sphere",
    ),
    "P(0) e P(1) sono reali": (
        "Universe.Epistemology.columnBorn_real",
        "Universe.Epistemology.ground_prob_real",
    ),
    "|z|² è la somma dei quadrati delle parti reale e immaginaria": (
        "Universe.Epistemology.modulus_squares",
        "Universe.Epistemology.modulus_imag_zero",
    ),
    "⟨ψ|Π₀|ψ⟩ = |α|²": ("Universe.Epistemology.projector_born",),
    "asse x: P(0) = 1 − s², P(1) = s²": (
        "Universe.Epistemology.axis_x_born0",
        "Universe.Epistemology.axis_x_born1",
    ),
    "asse z: |0⟩ è autostato, P(0) = 1": (
        "Universe.Epistemology.axis_z_born0",
        "Universe.Epistemology.axis_z_born1",
    ),
    "(A⊗B)⊗C e A⊗(B⊗C) sono lo stesso stato": (
        "Universe.Ontology.tensorIndexAssoc",
        "Universe.Composition.tensor_assoc",
        "Universe.Composition.tensor_assoc_ui",
        "Universe.Composition.tensor_assoc_obs",
    ),
    "|0⟩ ⊗ |0⟩ = |00⟩": ("Universe.Composition.ground_tensor",),
    "(U ⊗ I)(|ψ⟩ ⊗ |0⟩) riproduce le probabilità del primo fattore": (
        "Universe.Composition.kronecker_ui_gen",
        "Universe.Composition.marginal_left_gen",
    ),
    "(I ⊗ U)(|0⟩ ⊗ |ψ⟩) riproduce le probabilità del secondo fattore": (
        "Universe.Composition.kronecker_iu_gen",
        "Universe.Composition.marginal_right_gen",
    ),
    "CNOT² = I": ("Universe.Observer.cnot_involutive",),
    "‖CNOT v‖² = ‖v‖² su uno stato generico": ("Universe.Observer.cnot_norm",),
    "|ψ⟩ ⊗ |φ⟩ ha determinante zero": (
        "Universe.Observer.entangled_det",
        "Universe.Observer.product_det",
    ),
    "nel punto razionale, det CNOT(Φ|0⟩ ⊗ |0⟩) = −12/25 i": (
        "Universe.Observer.point_entangled",
        "Universe.Observer.point_not_product",
    ),
    "dopo CNOT il sistema ridotto è diagonale, con i pesi di Born": (
        "Universe.Observer.coherence_before",
        "Universe.Observer.decoherence",
    ),
    "l'apparato legge P(Φ|ψ⟩) su |0⟩ e sullo stato generico": (
        "Universe.Observer.pointer_born",
    ),
    "nel punto, la purezza del sistema ridotto è 337/625": (
        "Universe.Observer.point_purity",
    ),
    "due osservatori non sono mai in disaccordo": (
        "Universe.Observer.observers_agree",
        "Universe.Observer.observers_agree_right",
        "Universe.Observer.order_irrelevant",
        "Universe.Observer.order_irrelevant_right",
        "Universe.Observer.two_pointers",
        "Universe.Observer.two_pointers_right",
    ),
    "Wigner, leggendo l'amico, legge il sistema": (
        "Universe.Observer.chain_pointers",
        "Universe.Observer.chain_is_fanout",
        "Universe.Observer.cnot12_involutive",
    ),
    "Wigner e l'amico non sono mai in disaccordo": ("Universe.Observer.chain_agree",),
    "disfare l'amico restituisce la coerenza α β̄": (
        "Universe.Observer.friend_undone",
        "Universe.Observer.reduceSystem_product",
    ),
    "dopo la copia, disfare l'amico lascia il sistema diagonale": (
        "Universe.Observer.copy_irreversible",
    ),
    "Wigner conserva il peso di Born": ("Universe.Observer.wigner_keeps_record",),
    "nel punto, disfare l'amico dà coerenza 12/25 i e purezza 1": (
        "Universe.Observer.point_undone",
    ),
    "nel punto, dopo la copia: coerenza 0, purezza 337/625, pesi 9/25 e 16/25": (
        "Universe.Observer.point_copied",
    ),
    "un unitario locale sull'apparato non cambia i pesi del sistema": (
        "Universe.Observer.no_signalling_any_0",
        "Universe.Observer.no_signalling_any_1",
        "Universe.Observer.no_signalling_gen_0",
        "Universe.Observer.no_signalling_gen_1",
    ),
    "un unitario sul qubit di Wigner non cambia i pesi del sistema": (
        "Universe.Observer.no_signalling_wigner",
    ),
    "un unitario sul qubit dell'amico non cambia i pesi del sistema": (
        "Universe.Observer.no_signalling_friend",
    ),
    "un unitario su un altro qubit non cambia il marginale, n ≤ 4": (
        "Universe.Qubits.no_signalling_at",
    ),
    "la diagonale dello stato ridotto è il marginale, n ≤ 4": (
        "Universe.Qubits.reduceAt_diag",
    ),
    "su un prodotto lo stato ridotto è ‖resto‖² |ψ⟩⟨ψ|, n ≤ 4": (
        "Universe.Qubits.reduceAt_product",
    ),
    "U su un qubit qualsiasi di n conserva la norma, n ≤ 4": (
        "Universe.Qubits.norm_applyAt",
    ),
    "porte su qubit diversi commutano, n ≤ 4": ("Universe.Qubits.applyAt_comm",),
    "il fan-out su |ψ⟩ ⊗ |0…0⟩ è α|0…0⟩ + β|1…1⟩, n ≤ 5": (
        "Universe.Qubits.fanout_ghz",
    ),
    "nel fan-out ogni coppia di osservatori concorda, n ≤ 5": (
        "Universe.Qubits.fanout_agree",
    ),
    "dopo il fan-out il sistema è diagonale con i pesi di Born, n ≤ 5": (
        "Universe.Qubits.fanout_decoherence",
    ),
    "c = 3/5, s = 4/5, n = e_x: U†U = I nei razionali di Gauss": (
        "Universe.Epistemology.point_unitary",
    ),
    "nello stesso punto, P(0) = 9/25 e P(1) = 16/25": (
        "Universe.Epistemology.point_prob0",
        "Universe.Epistemology.point_prob1",
    ),
    "n = e_x: ⟨H⟩ = 0; n = e_z: ⟨H⟩ = 1, prima e dopo Φ": (
        "Universe.Symmetry.point_energy_x",
        "Universe.Symmetry.point_energy_z",
    ),
    "G³ = G e G² = |1⟩⟨1| ⊗ I": (
        "Universe.Interaction.generator_cube",
        "Universe.Series.expCoeff_idem",
    ),
    "(1 − G²) + c G² − i s G = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U": (
        "Universe.Interaction.controlled_from_hamiltonian",
    ),
    "nel punto c = 0, s = 1, n = e_x: α|00⟩ − i β|11⟩": (
        "Universe.Interaction.cnot_point",
        "Universe.Interaction.cnot_point_born",
    ),
    "la coerenza parziale è α β̄ · conj(⟨0|U|0⟩)": (
        "Universe.Interaction.partial_coherence",
    ),
    "la diagonale parziale è il peso di Born": (
        "Universe.Interaction.partial_diagonal",
    ),
    "tre punti della misura parziale, lungo e_x": (
        "Universe.Interaction.point_partial_flip",
        "Universe.Interaction.point_partial_idle",
        "Universe.Interaction.point_partial_mid",
    ),
    "dopo CNOT, la lettura 0 è (α, 0) e la lettura 1 è (0, β)": (
        "Universe.Composition.condition",
        "Universe.Interaction.luders",
    ),
    "una seconda lettura ripete l'esito e azzera l'altro": (
        "Universe.Interaction.repeatable",
    ),
    "nel punto, lo stato condizionato è 3/5|0⟩ e −4/5 i|1⟩": (
        "Universe.Interaction.point_luders",
    ),
    "nel punto, la seconda lettura ripete 9/25 e 16/25": (
        "Universe.Interaction.point_repeatable",
    ),
    "V(Uψ) = (V U V†)(Vψ) nell'anello libero": (
        "Universe.Symmetry.conj_evolution",
        "Universe.Symmetry.conj_inverse",
    ),
    "i pesi di Born di Vψ nella base V|k⟩ sono quelli di ψ": (
        "Universe.Symmetry.conj_born",
    ),
    "nel punto, V(U|0⟩) = −7/25 |0⟩ − 24/25 i |1⟩, pesi 1 e 0": (
        "Universe.Symmetry.point_conj_born",
        "Universe.Symmetry.point_conj_evolution",
    ),
    "V(Uψ) − (V U V†)(Vψ) sta in (gC, gN), con V = U": (
        "Universe.Symmetry.conj_evolution_law",
        "Universe.Symmetry.conj_evolution_rel",
    ),
    "i pesi di Born di Vψ nella base V|k⟩ e quelli di ψ stanno in (gC, gN)": (
        "Universe.Symmetry.conj_born_law",
        "Universe.Symmetry.conj_born_rel",
    ),
    "U(c₁, s₁) U(c₂, s₂) − U(c, s) sta nell'ideale di gN": (
        "Universe.Symmetry.evolution_compose",
    ),
    "U(c₁, s₁, n) U(c₂, s₂, m) = a I − i (b·σ) nell'anello libero": (
        "Universe.Symmetry.evolution_compose_axes",
    ),
    "a² + |b|² − 1 sta in (gC, gN, gC2, gM)": (
        "Universe.Symmetry.axes_norm_free",
        "Universe.Symmetry.compose_axes_norm",
    ),
    "nel punto, a = 9/25, b = (12/25, −16/25, 12/25) e "
    "UₙUₘ|0⟩ = (9/25 − 12/25 i)|0⟩ + (−16/25 − 12/25 i)|1⟩": (
        "Universe.Symmetry.point_axes",
    ),
    "UₙUₘ|0⟩ e UₘUₙ|0⟩ differiscono su |1⟩, con pesi 9/25 e 16/25": (
        "Universe.Symmetry.rotations_noncommute",
    ),
    "se le due coppie stanno sul cerchio, ci sta (c, s)": (
        "Universe.Symmetry.compose_circle",
    ),
    "nel punto, U|0⟩ = −7/25 |0⟩ − 24/25 i |1⟩ con c = −7/25, s = 24/25": (
        "Universe.Symmetry.compose_circle",
        "Universe.Symmetry.evolution_compose",
        "Universe.Symmetry.point_compose",
    ),
    "la legge di addizione di coseno e seno, a ogni grado": (
        "Universe.Angle.angle_add_cos",
        "Universe.Angle.angle_add_sin",
    ),
}
