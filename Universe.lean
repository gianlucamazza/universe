/-
Kernel formale. Il corrispondente eseguibile sta nel pacchetto Python `universe`.
Le identità si ripartiscono in libero, ideale `(gC, gN)`, ideale `(gC, gN, gA)`,
ideale `(gN)`, `(gC, gC2)` e `(gC, gN, gC2, gM)`.
La nota è `papers/qubit.md`.

`Universe.Ring` è lo scalare `ℚ(i)`.
`Universe.Quotient` è il quoziente `c² + s² = 1`, `|n| = 1`, con cofattori.
`reduce_sound` ricostruisce i coefficienti. `Universe.Dynamics.reduce_complete`
è il converso: se `p` sta in `(gC, gN)`, ogni coefficiente di `(reduce p).rem` è zero.
`gA`, nello stesso file, è la sfera delle ampiezze e non entra in `reduce`.
`Universe.Series` è il collasso di `exp(-i φ a)` quando `a² = 1`.
`Universe.Angle` somma `cosCoeff k · φᵏ / k!` e `sinCoeff`.
`angle_add_cos` e `angle_add_sin` sono la legge di addizione a ogni grado.
`circle_tail` scrive `C_N² + S_N² − 1` come coda. `circle_bound` la stima
con `remainder`, e `exp_add` è la legge di addizione di `xᵏ / k!`.
`group_bound_cos` e `group_bound_sin` stimano la legge di gruppo troncata
con la coda di `exp(|x| + |y|)`. Se `2|x| ≤ (N + 2) / 2`, `remainder_small`
chiude `remainder` con il doppio del primo termine. `angle_born` legge,
lungo `e_x` e per ogni `N` e ogni `φ` razionale, `U|0⟩` nel punto
`(C_N(φ), S_N(φ))`: ampiezze `C_N` e `−i S_N`, pesi di Born i quadrati,
somma entro `remainder` da `1`. `angle_half` è `φ = 1/2`, `N = 4`.
`Universe.Dynamics` è l'algebra delle matrici su quel quoziente.
`Universe.Evaluation` dice che `evalAt` rispetta `polySame`, il prodotto e il coniugio.
`Universe.Qubit` istanzia `expCoeff` sull'Hamiltoniana e prova `U†U`, `UU†`,
`det U − 1` e `ψ†(U†U)ψ − ‖ψ‖²` per ampiezze arbitrarie, con cofattori `gC + s² · gN`.
`Universe.Epistemology.ground_prob_sum` è `P(0) + P(1) − 1` su `Φ|0⟩`,
con gli stessi cofattori `gC + s² · gN`.
`modulus_squares` è `|z|² = re² + im²` nell'anello libero, per ogni polinomio.
`modulus_imag_zero` dice che quei coefficienti sono razionali.
`columnBorn_real` è lo stesso fatto per ogni peso di Born, e `ground_prob_real`
è il caso di `Φ|0⟩`. `projector_born` è `⟨ψ|Π₀|ψ⟩ = |α|²`, con `Π₀ = diag(1, 0)`.
`sphere_prob_sum` mette `ψ†(U†U)ψ − 1`, sullo stato generico, nell'ideale
`(gC, gN, gA)` con tre cofattori. `literal_sandwich` dice che `|γ₀|² + |γ₁|²`
e `ψ†(U†U)ψ` hanno gli stessi coefficienti, per ogni matrice.
`literal_evolution_norm` trasporta la norma sul modulo letterale, e
`literal_sphere` trasporta la sfera su `‖Uψ‖² − 1`. `reduce` sbuccia ancora
solo `c²` e `nx²`.
`keepX` e `keepZ` specializzano un asse. `specX_pmul` e `specZ_pmul` commutano
con il prodotto, `specX_conj` e `specZ_conj` con il coniugio. `axis_x_born0`
è `spec keepX groundP0 − (1 − s²) = gC`, `axis_x_born1` è `spec groundP1 = s²`,
`axis_x_gn` azzera i coefficienti di `gN`. `axis_z_born1` dice che il secondo
peso è il polinomio zero, `axis_z_born0` è `spec keepZ groundP0 − 1 = gC`,
e `axis_z_gn` azzera i coefficienti di `gN` lungo z.
`eval_prob_axis_x` valuta quei pesi lungo `e_x` per ogni `c` e `s`.
`point_prob0` e `point_prob1` sono il caso `c = 3/5`, `s = 4/5`.
`point_gC` e `point_gN` sono i due vincoli in `ℚ`, e `point_unitary` valuta `δ`
in `n = e_x`.
`Universe.Ontology` è X. `tensorIndexAssoc` è l'associatività degli indici.
`tensorIndex_assoc_qubit` è quel passo sulle dimensioni `2` e `2`.
`tensor_assoc` identifica le due parentesizzazioni di tre qubit.
`tensor_assoc_ui` porta `(U ⊗ I ⊗ I)` sul primo fattore.
`tensor_assoc_obs` identifica i moduli quadri delle otto celle.
`point_cells` li valuta su tre copie di `Φ|0⟩` nel punto:
`729/15625`, …, `4096/15625`.
`Universe.Composition.tensorIndex` è `right * i + k`. `ground_tensor` dice che
`|0⟩ ⊗ |0⟩` ha ampiezza `1` nella cella `0` e `0` altrove.
`kronecker_ui_gen` è `(U ⊗ I)(|ψ⟩ ⊗ |φ⟩) = (U|ψ⟩) ⊗ |φ⟩` per ogni matrice e
ogni coppia. `marginal_left_gen` è `‖φ‖² · P(U|ψ⟩)`. Con `|φ⟩ = |0⟩` la norma
è la costante `1` e si ritrova `marginal_ui`. `kronecker_iu_gen` e
`marginal_right_gen` scambiano i fattori. Sul fattore generico il cofattore
di `gA` è `marginal_left_sphere`.
`Universe.Observer.applyCNOT` scambia `|10⟩` e `|11⟩`: `cnot_norm` e
`product_det` stanno nell'anello libero, e `point_entangled` valuta il
determinante di `CNOT(Φ|0⟩ ⊗ |0⟩)` in `−12/25 i`. `point_not_product`
dice che quel valore non è un prodotto di due vettori di `ℚ(i)`.
`reduceLeft` traccia il fattore destro. `decoherence` azzera
l'antidiagonale nell'anello libero, e `pointer_born` ricava `Obs` come
diagonale dell'apparato dopo `Φ`. `point_purity` valuta la purezza del
sistema ridotto in `337/625`.
`cnot01` e `cnot02` danno `α|000⟩ + β|111⟩`: i due apparati non sono mai
in disaccordo, in entrambi gli ordini e su entrambe le parentesizzazioni.
`cnot12` legge l'amico: `chain_pointers` è lo stesso stato,
`chain_is_fanout` lo identifica col fan-out, `chain_agree` è l'accordo.
`reduceSystem` traccia amico e Wigner. `friend_undone` restituisce
`α conj(β)`. `copy_irreversible` lascia `α|000⟩ + β|101⟩` con il
sistema diagonale, e `wigner_keeps_record` conserva `bornPair`.
`point_undone` valuta, su `Φ|0⟩` nel punto, coerenza `12/25 i` e
purezza `1`. `point_copied` valuta coerenza `0`, purezza `337/625`
e i pesi di Wigner `9/25`, `16/25`.
`no_signalling_0` e `no_signalling_1` dicono che `I ⊗ U` sull'apparato,
dopo `CNOT` con `|0⟩`, cambia il marginale del sistema di un polinomio
in `(gC, gN)`. `no_signalling_any_0` e `no_signalling_any_1` lo dicono
per ogni stato di due qubit; `no_signalling_gen_0` e `no_signalling_gen_1`
sono il caso `genericQuad`. `no_signalling_wigner` e `no_signalling_friend`
lo dicono per ogni stato di tre qubit: un unitario sul qubit di Wigner,
o su quello dell'amico, lascia la diagonale di `reduceSystem` in `(gC, gN)`.
`Universe.Symmetry` dice che `U` commuta con `H` nell'anello libero
(`evolution_commutes_hamiltonian`): `UH` e `HU` sono `c H − i s H²`.
`energy_conserved` mette `⟨Uψ|H|Uψ⟩ − ⟨ψ|H|ψ⟩` in `(gC, gN)`, per ogni
ampiezza. Nel punto razionale `⟨0|H|0⟩` vale `0` lungo `e_x` e `1` lungo
`e_z`, prima e dopo `Φ` (`point_energy_x`, `point_energy_z`).
`evolution_compose` mette `U(c₁, s₁) U(c₂, s₂) − U(c₁c₂ − s₁s₂, s₁c₂ + c₁s₂)`
nell'ideale di `gN`: l'unica regola è `H² = I`. `evolution_compose_axes`
mette `U(c₁, s₁, n) U(c₂, s₂, m)` uguale a `a I − i (b·σ)` nell'anello
libero, e `compose_axes_same` ritrova la legge sullo stesso asse, modulo
`gN`. `axes_norm_free` è `a² + |b|² = (c₁² + s₁² |n|²)(c₂² + s₂² |m|²)`
nell'anello libero, e `compose_axes_norm` mette `a² + |b|² − 1` in
`(gC, gN, gC2, gM)`. `gM = mx² + my² + mz² − 1` resta fuori da `reduce`.
`evalAt3` legge `mx my mz` e coincide con `evalAt2` senza quegli esponenti.
Nel punto `n = e_x`, `m = e_z`, `point_axes` valuta `a`, `b` e `Uₙ Uₘ |0⟩`.
`rotations_noncommute` dice che `Uₘ Uₙ |0⟩` differisce sull'ampiezza di
`|1⟩`, con gli stessi pesi di Born.
`compose_circle` mette
`c² + s² − 1` in `(gC, gC2)`, e `gC2` resta fuori da `reduce`.
`conj_evolution_rel` e `conj_born_rel` portano il cambio di base
nell'ideale `(gC, gN)`. Con `V = U` sono `conj_evolution_law` e
`conj_born_law`. `point_compose` valuta l'angolo composto con `evalAt2`.
`Universe.Interaction` costruisce `G = |1⟩⟨1| ⊗ H`. `generator_cube` è
`G³ = G`. `controlled_from_hamiltonian` è l'evoluzione controllata, e
`cnot_point` la legge nel punto `c = 0`, `s = 1`, `n = e_x` come `CNOT`
seguito dalla fase `−i`. `cnot_point_born` dice che quella fase esce dai
pesi di Born. `point_cnot_sample` valuta `3/5|00⟩ − 4/5|11⟩`, con pesi
`9/25` e `16/25`. Con l'apparato in `|0⟩`, `partial_coherence` dà
l'antidiagonale `α β̄ · conj(⟨0|U|0⟩)` nell'anello libero, con
`⟨0|U|0⟩ = c − i s nz`, e `partial_diagonal` mette la diagonale su
`bornPair` modulo `(gC, gN)`. I tre punti lungo `e_x` sono
`point_partial_idle`, `point_partial_mid` e `point_partial_flip`.
`luders` è la lettura del puntatore dopo `CNOT`: `(α, 0)` e `(0, β)`,
con norme `bornPair`. `repeatable` ripete l'esito su un apparato fresco.
Nel punto le norme sono `9/25` e `16/25`.
`Universe.Qubits` è un albero binario perfetto di `n` qubit. `applyAt`
applica una matrice `2×2` al qubit `k`: sul bit alto mescola le branche
foglia per foglia, e sul qubit `k + 1` agisce nei due figli.
`norm_applyAt` mette `‖applyAt k U v‖² − ‖v‖²` in `(gC, gN)`.
`marginalAt` è la coppia di Born di un qubit. `no_signalling_at` la lascia
in `(gC, gN)` quando il unitario agisce su un qubit diverso.
`applyAt_comm` fa commutare due matrici su qubit diversi. `reduceAt` è
la traccia parziale su un qubit. `cnotFrom0` è il `CNOT` dal qubit `0`.
`fanout` li applica tutti su `|ψ⟩ ⊗ |0…0⟩`: `fanout_ghz` è
`α|0…0⟩ + β|1…1⟩`, `fanout_agree` azzera il peso delle celle in cui
due qubit differiscono, e `fanout_decoherence` rende il sistema
diagonale con `bornPair`, per `n ≥ 2`.
`Universe.Points` è la tabella dei punti razionali. Ogni voce è il
membro sinistro del teorema che la dimostra. `lake exe points` la stampa.
-/
import Universe.Angle
import Universe.Composition
import Universe.Dynamics
import Universe.Epistemology
import Universe.Evaluation
import Universe.Interaction
import Universe.Observer
import Universe.Ontology
import Universe.Points
import Universe.Qubit
import Universe.Qubits
import Universe.Quotient
import Universe.Ring
import Universe.Series
import Universe.Symmetry
