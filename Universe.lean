/-
Kernel formale. Il corrispondente eseguibile sta nel pacchetto Python `universe`.
Le identità si ripartiscono in libero, ideale `(gC, gN)` e ideale `(gC, gN, gA)`.
La nota è `papers/qubit.md`.

`Universe.Ring` è lo scalare `ℚ(i)`.
`Universe.Quotient` è il quoziente `c² + s² = 1`, `|n| = 1`, con cofattori.
`reduce_sound` ricostruisce i coefficienti. `Universe.Dynamics.reduce_complete`
è il converso: se `p` sta in `(gC, gN)`, ogni coefficiente di `(reduce p).rem` è zero.
`gA`, nello stesso file, è la sfera delle ampiezze e non entra in `reduce`.
`Universe.Series` è il collasso di `exp(-i φ a)` quando `a² = 1`.
`Universe.Dynamics` è l'algebra delle matrici su quel quoziente.
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
`point_prob0` e `point_prob1` valutano quei pesi in `c = 3/5`, `s = 4/5`.
`point_gC` e `point_gN` sono i due vincoli in `ℚ`, e `point_unitary` valuta `δ`
in `n = e_x`.
`Universe.Ontology` è X. `tensorIndexAssoc` è l'associatività degli indici.
`tensorIndex_assoc_qubit` è quel passo sulle dimensioni `2` e `2`.
`tensor_assoc` identifica le due parentesizzazioni di tre qubit.
`tensor_assoc_ui` porta `(U ⊗ I ⊗ I)` sul primo fattore.
`tensor_assoc_obs` identifica i moduli quadri delle otto celle.
`Universe.Composition.tensorIndex` è `right * i + k`. `ground_tensor` dice che
`|0⟩ ⊗ |0⟩` ha ampiezza `1` nella cella `0` e `0` altrove.
`kronecker_ui_gen` è `(U ⊗ I)(|ψ⟩ ⊗ |φ⟩) = (U|ψ⟩) ⊗ |φ⟩` per ogni matrice e
ogni coppia. `marginal_left_gen` è `‖φ‖² · P(U|ψ⟩)`. Con `|φ⟩ = |0⟩` la norma
è la costante `1` e si ritrova `marginal_ui`. `kronecker_iu_gen` e
`marginal_right_gen` scambiano i fattori. Sul fattore generico il cofattore
di `gA` è `marginal_left_sphere`.
-/
import Universe.Composition
import Universe.Dynamics
import Universe.Epistemology
import Universe.Ontology
import Universe.Qubit
import Universe.Quotient
import Universe.Ring
import Universe.Series
