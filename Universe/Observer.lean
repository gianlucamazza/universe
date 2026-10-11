/-
CNOT, il primo stato entangled, e l'osservatore interno.

`applyCNOT` scambia `|10⟩` e `|11⟩`. Su `|ψ⟩ ⊗ |0⟩` resta `α|00⟩ + β|11⟩`.
`quadDet` è zero su ogni prodotto, nell'anello libero. Nel punto
`c = 3/5`, `s = 4/5`, `n = e_x` il determinante di `CNOT(Φ|0⟩ ⊗ |0⟩)`
è `−12/25 i`, quindi quello stato non è un prodotto.

`reduceLeft` è la traccia parziale sul fattore destro. Senza interazione
il sistema resta puro, a meno di `‖φ‖²`. Dopo `CNOT` la coerenza è il
polinomio zero e la diagonale è `bornPair`. `pointer_born` legge quegli
stessi pesi sull'apparato: `Obs` è quel teorema. La purezza scende a
`|α|⁴ + |β|⁴`. Sulla sfera il difetto ha cofattore `gA`. Nel punto vale
`337/625`. `eval_purity` porta `Tr(ρ²)` sulle quattro entrate.

Due apparati. `cnot01` e `cnot02` agiscono sul bit medio e sul bit basso.
Su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩` entrambi gli ordini danno `α|000⟩ + β|111⟩`. I pesi
di Born delle celle 1–6 sono il polinomio zero: i due apparati non sono
mai in disaccordo. `tensor_assoc` porta gli stessi fatti sulla
parentesizzazione destra. Tutto sta nell'anello libero.

`cnot12` è il `CNOT` di Wigner sull'amico: controllo sul bit medio,
bersaglio sul bit basso, celle `2↔3` e `6↔7`. È un'involuzione.
`cnot12 ∘ cnot01` su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩` è `α|000⟩ + β|111⟩`, lo stesso
stato di `cnot02 ∘ cnot01`. I pesi di Born sono quelli di
`observers_agree`: Wigner e l'amico non discordano.

`reduceSystem` traccia amico e Wigner. Su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩` è `|ψ⟩⟨ψ|`.
`cnot01` due volte restituisce quello stato e la coerenza `α conj(β)`.
Dopo la copia `cnot12`, la stessa porta lascia `α|000⟩ + β|101⟩`: le
entrate fuori diagonale sono il polinomio zero, la diagonale è
`bornPair`, e il marginale di Wigner resta `bornPair`.

Nel punto `c = 3/5`, `s = 4/5`, `n = e_x`, con `ψ = Φ|0⟩`, disfare
l'amico restituisce coerenza `12/25 i` e purezza `1`. Dopo la copia
la coerenza è `0`, la purezza è `337/625` e Wigner legge `9/25`,
`16/25`.

`I ⊗ U` sull'apparato, dopo `CNOT` con `|0⟩`, non cambia il marginale
del sistema. La differenza sta in `(gC, gN)`: i cofattori di `δ`
moltiplicati per `|α|²` e per `|β|²`. Lo stesso conto vale per ogni
`Quad`: ogni blocco dell'apparato è `‖Uγ‖² − ‖γ‖²`, e i termini
incrociati sono l'entrata fuori diagonale di `U†U`. `genericQuad`
è il caso delle quattro ampiezze libere.

Lo stesso argomento sui tre qubit, per ogni `Oct`. `I ⊗ I ⊗ U` sul
qubit di Wigner e `I ⊗ U ⊗ I` sul qubit dell'amico lasciano la
diagonale di `reduceSystem` in `(gC, gN)`. Quel marginale è la somma
di due norme di un qubit, e ciascuna è `literal_evolution_norm`.
`no_signalling_any_0`, `no_signalling_any_1`, `no_signalling_wigner` e
`no_signalling_friend` sono i casi `n = 2` e `n = 3` di
`no_signalling_at`. `reduce_product` è `reduceAt_product` sul qubit `0`.
-/
import Universe.Composition
import Universe.Epistemology
import Universe.Evaluation
import Universe.Qubit
import Universe.Qubits

namespace Universe.Observer

open Universe.Ring
open Universe.Quotient hiding mul
open Universe.Dynamics
open Universe.Epistemology
open Universe.Evaluation
open Universe.Composition
open Universe.Qubit
open Universe.Qubits

/-- Controllo a sinistra, bersaglio a destra. Su `2 * i + k` scambia `|10⟩` e `|11⟩`. -/
def applyCNOT (v : Quad) : Quad := ⟨v.a0, v.a1, v.a3, v.a2⟩

/-- `CNOT` è un'involuzione. -/
theorem cnot_involutive (v : Quad) : applyCNOT (applyCNOT v) = v := by
  cases v
  rfl

/-- `CNOT(|ψ⟩ ⊗ |0⟩) = α|00⟩ + β|11⟩`. -/
theorem cnot_ket0 (ψ : Pair) :
    applyCNOT (tensorPair ψ ket0) = ⟨ψ.a0, [], [], ψ.a1⟩ := by
  rw [tensor_idle_right]
  rfl

/-- Somma dei quattro moduli quadri. -/
def quadNorm (v : Quad) : Poly :=
  columnBorn v.a0 ++ columnBorn v.a1 ++ columnBorn v.a2 ++ columnBorn v.a3

/-- Gli ultimi due addendi si scambiano nei coefficienti. -/
theorem polySame_swap_last (p c d : Poly) :
    polySame ((p ++ d) ++ c) ((p ++ c) ++ d) := by
  intro t
  rw [coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append]
  calc
    (coeffOf p t + coeffOf d t) + coeffOf c t
        = coeffOf p t + (coeffOf d t + coeffOf c t) := by rw [Gauss.add_assoc]
    _ = coeffOf p t + (coeffOf c t + coeffOf d t) := by
          rw [Gauss.add_comm (coeffOf d t) (coeffOf c t)]
    _ = (coeffOf p t + coeffOf c t) + coeffOf d t := by rw [← Gauss.add_assoc]

/-- `CNOT` conserva la somma dei moduli quadri, nell'anello libero. -/
theorem cnot_norm (v : Quad) : polySame (quadNorm (applyCNOT v)) (quadNorm v) := by
  simp only [quadNorm, applyCNOT]
  exact polySame_swap_last (columnBorn v.a0 ++ columnBorn v.a1)
    (columnBorn v.a2) (columnBorn v.a3)

/-- `a₀ a₃ − a₁ a₂`. -/
def quadDet (v : Quad) : Poly := psub (pmul v.a0 v.a3) (pmul v.a1 v.a2)

/-- Ogni stato prodotto ha determinante zero. -/
theorem product_det (ψ φ : Pair) : polySame (quadDet (tensorPair ψ φ)) [] := by
  simp only [quadDet, tensorPair]
  intro t
  have hleft := polySame_assoc_comm ψ.a0 φ.a0 ψ.a1 φ.a1
  have hright := polySame_assoc_comm ψ.a0 φ.a1 ψ.a1 φ.a0
  have htail : polySame (pmul (pmul ψ.a0 ψ.a1) (pmul φ.a1 φ.a0))
      (pmul (pmul ψ.a0 ψ.a1) (pmul φ.a0 φ.a1)) :=
    polySame_pmul_right (polySame_mul_comm φ.a1 φ.a0) (pmul ψ.a0 ψ.a1)
  have heq :=
    polySame.trans hleft (polySame.trans (polySame.symm htail) (polySame.symm hright))
  rw [coeff_psub, heq t, Gauss.add_neg_cancel, coeffOf_nil]

/-- Il determinante di `α|00⟩ + β|11⟩` è `α β`. -/
theorem entangled_det (ψ : Pair) :
    polySame (quadDet (applyCNOT (tensorPair ψ ket0))) (pmul ψ.a0 ψ.a1) := by
  rw [cnot_ket0]
  simp only [quadDet, pmul_nil_left, psub, pneg]
  exact polySame_append_nil _

theorem mulMono_single (a b : Gauss) (m n : Mono) :
    mulMono a m (single b n) = single (a * b) (m.mul n) := by
  simp [mulMono, single]

theorem pmul_single_append (a : Gauss) (m : Mono) (p q : Poly) :
    pmul (single a m) (p ++ q) = (mulMono a m p ++ mulMono a m q) ++ [] := by
  rw [pmul_single_list, mulMono_append]

/-- `3/5`, prima ampiezza di `Φ|0⟩` lungo x nel punto. -/
def pointAlpha : Gauss := ⟨pointC, 0⟩

/-- `−4/5 i`, seconda ampiezza di `Φ|0⟩` lungo x nel punto. -/
def pointBeta : Gauss := ⟨0, -pointS⟩

theorem point_alpha :
    evalAt pointC pointS 1 0 0 (specPoly keepX evolution.a00) = pointAlpha := by
  rw [specX_a00, eval_single]
  ext <;> simp [pointAlpha, monoVal, powR, c1, pointC, pointS, Gauss.re_one,
    Gauss.im_one] <;> grind

theorem point_beta :
    evalAt pointC pointS 1 0 0 (specPoly keepX evolution.a10) = pointBeta := by
  rw [specX_a10, eval_single]
  ext <;> simp [pointBeta, monoVal, powR, s1, pointC, pointS, Gauss.re_neg,
    Gauss.im_neg, Gauss.re_i, Gauss.im_i] <;> grind

/-- Le quattro celle di `CNOT(Φ|0⟩ ⊗ |0⟩)`, dopo `n = e_x`, valutate nel punto. -/
theorem point_bell :
    evalAt pointC pointS 1 0 0
        (specPoly keepX (applyCNOT (tensorPair (applyMat evolution ket0) ket0)).a0) =
      pointAlpha ∧
    evalAt pointC pointS 1 0 0
        (specPoly keepX (applyCNOT (tensorPair (applyMat evolution ket0) ket0)).a1) = 0 ∧
    evalAt pointC pointS 1 0 0
        (specPoly keepX (applyCNOT (tensorPair (applyMat evolution ket0) ket0)).a2) = 0 ∧
    evalAt pointC pointS 1 0 0
        (specPoly keepX (applyCNOT (tensorPair (applyMat evolution ket0) ket0)).a3) =
      pointBeta := by
  have hket : applyMat evolution ket0 = ⟨evolution.a00, evolution.a10⟩ := by
    simp only [applyMat, ket0, pmul_one, pmul_nil, List.append_nil]
  rw [cnot_ket0, hket]
  refine ⟨point_alpha, ?_, ?_, point_beta⟩
  · simp [specPoly, evalAt]
  · simp [specPoly, evalAt]

theorem point_amp_mul : pointAlpha * pointBeta = ⟨0, -((12 : Rat) / 25)⟩ := by
  simp only [pointAlpha, pointBeta, pointC, pointS]
  ext <;> simp <;> grind

/-- Nel punto il determinante vale `−12/25 i`. -/
theorem point_entangled :
    evalAt pointC pointS 1 0 0
        (specPoly keepX
          (quadDet (applyCNOT (tensorPair (applyMat evolution ket0) ket0)))) =
      ⟨0, -((12 : Rat) / 25)⟩ := by
  rw [cnot_ket0]
  simp only [quadDet, applyMat, ket0, pmul_one, pmul_nil, List.append_nil, psub, pneg]
  rw [evolution_a00_bin, evolution_a10_bin, pmul_append_left, pmul_single_append,
    pmul_single_append, mulMono_single, mulMono_single, mulMono_single, mulMono_single]
  repeat rw [spec_append]
  simp [specPoly, keepX, single, c1, s1, nx1, ny1, nz1, Mono.mul, evalAt,
    Gauss.add_zero, monoVal, powR, pointC, pointS]
  grind

/-- I due prodotti di Gauss hanno lo stesso determinante `x₀ y₀ · x₁ y₁`. -/
theorem gauss_prod_det (x0 x1 y0 y1 : Gauss) :
    (x0 * y0) * (x1 * y1) = (x0 * y1) * (x1 * y0) := by
  calc
    (x0 * y0) * (x1 * y1) = x0 * (y0 * (x1 * y1)) := by rw [Gauss.mul_assoc x0 y0 (x1 * y1)]
    _ = x0 * ((y0 * x1) * y1) := by rw [Gauss.mul_assoc y0 x1 y1]
    _ = x0 * ((x1 * y0) * y1) := by rw [Gauss.mul_comm y0 x1]
    _ = x0 * (x1 * (y0 * y1)) := by rw [Gauss.mul_assoc x1 y0 y1]
    _ = (x0 * x1) * (y0 * y1) := by rw [← Gauss.mul_assoc x0 x1 (y0 * y1)]
    _ = (x0 * x1) * (y1 * y0) := by rw [Gauss.mul_comm y0 y1]
    _ = x0 * (x1 * (y1 * y0)) := by rw [Gauss.mul_assoc x0 x1 (y1 * y0)]
    _ = x0 * ((x1 * y1) * y0) := by rw [← Gauss.mul_assoc x1 y1 y0]
    _ = x0 * ((y1 * x1) * y0) := by rw [Gauss.mul_comm x1 y1]
    _ = x0 * (y1 * (x1 * y0)) := by rw [Gauss.mul_assoc y1 x1 y0]
    _ = (x0 * y1) * (x1 * y0) := by rw [← Gauss.mul_assoc x0 y1 (x1 * y0)]

theorem point_det_ne : (⟨0, -((12 : Rat) / 25)⟩ : Gauss) ≠ 0 := by
  intro h
  have him : -((12 : Rat) / 25) = 0 := by simpa using congrArg Gauss.im h
  grind

/-- Nessuna coppia di vettori di `ℚ(i)` ha per tensore il `Quad` valutato. -/
theorem point_not_product :
    ¬ ∃ x0 x1 y0 y1 : Gauss,
      x0 * y0 = pointAlpha ∧ x0 * y1 = 0 ∧ x1 * y0 = 0 ∧ x1 * y1 = pointBeta := by
  rintro ⟨x0, x1, y0, y1, h00, h01, h10, h11⟩
  have hzero : pointAlpha * pointBeta = 0 := by
    calc
      pointAlpha * pointBeta = (x0 * y0) * (x1 * y1) := by rw [h00, h11]
      _ = (x0 * y1) * (x1 * y0) := gauss_prod_det x0 x1 y0 y1
      _ = 0 * 0 := by rw [h01, h10]
      _ = 0 := by rw [Gauss.zero_mul]
  rw [point_amp_mul] at hzero
  exact point_det_ne hzero

/-! ### Traccia parziale -/

/-- Traccia parziale sul fattore destro. La diagonale è `marginalLeft`. -/
def reduceLeft (v : Quad) : Mat where
  a00 := columnBorn v.a0 ++ columnBorn v.a1
  a01 := pmul v.a0 (conjP v.a2) ++ pmul v.a1 (conjP v.a3)
  a10 := pmul v.a2 (conjP v.a0) ++ pmul v.a3 (conjP v.a1)
  a11 := columnBorn v.a2 ++ columnBorn v.a3

/-- Traccia parziale sul fattore sinistro. La diagonale è `marginalRight`. -/
def reduceRight (v : Quad) : Mat where
  a00 := columnBorn v.a0 ++ columnBorn v.a2
  a01 := pmul v.a0 (conjP v.a1) ++ pmul v.a2 (conjP v.a3)
  a10 := pmul v.a1 (conjP v.a0) ++ pmul v.a3 (conjP v.a2)
  a11 := columnBorn v.a1 ++ columnBorn v.a3

/-- La diagonale dello stato ridotto è il marginale sinistro. -/
theorem reduceLeft_diag (v : Quad) :
    ⟨(reduceLeft v).a00, (reduceLeft v).a11⟩ = marginalLeft v := rfl

/-- Senza interazione il sistema resta puro, a meno di `‖φ‖²`.

È `reduceAt_product` sul qubit `0`: il resto è `|φ⟩`. -/
theorem reduce_product (ψ φ : Pair) :
    matSame (reduceLeft (tensorPair ψ φ)) (matScale (normPair φ) (outer ψ)) :=
  reduceAt_product ψ (0 : Fin 2) (ofPair φ)

/-- Prima di `CNOT` la coerenza `α conj(β)` è ancora nello stato ridotto. -/
theorem coherence_before (ψ : Pair) :
    polySame (reduceLeft (tensorPair ψ ket0)).a01 (pmul ψ.a0 (conjP ψ.a1)) := by
  rw [tensor_idle_right]
  simp only [reduceLeft, conjP, pmul_nil]
  exact polySame_append_nil _

/-- Dopo `CNOT` lo stato ridotto del sistema è diagonale, con diagonale `bornPair`.

L'identità sta nell'anello libero. -/
theorem decoherence (ψ : Pair) :
    polySame (reduceLeft (applyCNOT (tensorPair ψ ket0))).a01 [] ∧
      polySame (reduceLeft (applyCNOT (tensorPair ψ ket0))).a10 [] ∧
        pairSame ⟨(reduceLeft (applyCNOT (tensorPair ψ ket0))).a00,
            (reduceLeft (applyCNOT (tensorPair ψ ket0))).a11⟩ (bornPair ψ) := by
  rw [cnot_ket0]
  simp only [reduceLeft, bornPair, columnBorn_nil, conjP, pmul_nil, pmul_nil_left,
    List.append_nil, List.nil_append]
  exact ⟨polySame_refl _, polySame_refl _, polySame_refl _, polySame_refl _⟩

/-- L'apparato in `|0⟩`, dopo `CNOT`, legge `bornPair ψ` sulla propria diagonale. -/
theorem pointer_diag (ψ : Pair) :
    polySame (reduceRight (applyCNOT (tensorPair ψ ket0))).a01 [] ∧
      polySame (reduceRight (applyCNOT (tensorPair ψ ket0))).a10 [] ∧
        pairSame ⟨(reduceRight (applyCNOT (tensorPair ψ ket0))).a00,
            (reduceRight (applyCNOT (tensorPair ψ ket0))).a11⟩ (bornPair ψ) := by
  rw [cnot_ket0]
  simp only [reduceRight, bornPair, columnBorn_nil, conjP, pmul_nil, pmul_nil_left,
    List.append_nil, List.nil_append]
  exact ⟨polySame_refl _, polySame_refl _, polySame_refl _, polySame_refl _⟩

/-- L'apparato, che è un sottosistema, legge i pesi di Born del sistema evoluto.

`Obs` è ora un teorema: dopo `CNOT` con un apparato in `|0⟩`, i pesi di
`Φ|ψ⟩` sono la diagonale dello stato ridotto dell'apparato. -/
theorem pointer_born (ψ : Pair) :
    polySame (reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))).a01 [] ∧
      polySame (reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))).a10 [] ∧
        pairSame ⟨(reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))).a00,
            (reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))).a11⟩
          (bornPair (applyMat evolution ψ)) :=
  pointer_diag (applyMat evolution ψ)

/-! ### Purezza -/

/-- Traccia di una matrice `2×2`. -/
def matTrace (M : Mat) : Poly := M.a00 ++ M.a11

/-- `Tr(ρ²)`. -/
def purity (ρ : Mat) : Poly := matTrace (matMul ρ ρ)

/-- `eval` porta `Tr(ρ²)` sul quadrato delle quattro entrate. -/
theorem eval_purity (c s nx ny nz : Rat) (ρ : Mat) :
    evalAt c s nx ny nz (purity ρ) =
      (evalAt c s nx ny nz ρ.a00 * evalAt c s nx ny nz ρ.a00 +
          evalAt c s nx ny nz ρ.a01 * evalAt c s nx ny nz ρ.a10) +
        (evalAt c s nx ny nz ρ.a10 * evalAt c s nx ny nz ρ.a01 +
          evalAt c s nx ny nz ρ.a11 * evalAt c s nx ny nz ρ.a11) := by
  simp only [purity, matTrace, matMul]
  rw [eval_append, eval_append, eval_append, eval_pmul, eval_pmul, eval_pmul, eval_pmul]

/-- I due prodotti `α conj(β) · β conj(α)` e `|α|² |β|²` hanno gli stessi coefficienti. -/
theorem cross_born (α β : Poly) :
    polySame (pmul (pmul α (conjP β)) (pmul β (conjP α)))
      (pmul (columnBorn α) (columnBorn β)) :=
  polySame.trans (polySame_assoc_comm α (conjP β) β (conjP α))
    (polySame.trans
      (polySame_pmul_right (polySame_mul_comm (conjP β) (conjP α)) (pmul α β))
      (polySame.symm (polySame_assoc_comm α (conjP α) β (conjP β))))

/-- `(p + q)²` espanso nei quattro prodotti. -/
theorem square_expand (p q : Poly) :
    polySame (pmul (p ++ q) (p ++ q))
      ((pmul p p ++ pmul p q) ++ (pmul q p ++ pmul q q)) :=
  polySame.trans (fun _ => by rw [pmul_append_left])
    (polySame_append (polySame_mul_append_right p p q) (polySame_mul_append_right q p q))

/-- Prima dell'interazione la purezza di `|ψ⟩⟨ψ|` è `‖ψ‖⁴`. -/
theorem purity_before (ψ : Pair) :
    polySame (purity (outer ψ)) (pmul (normPair ψ) (normPair ψ)) := by
  simp only [purity, matTrace, matMul, outer, normPair]
  exact polySame.trans
    (polySame_append
      (polySame_append (polySame_refl _) (cross_born ψ.a0 ψ.a1))
      (polySame_append (cross_born ψ.a1 ψ.a0) (polySame_refl _)))
    (polySame.symm (square_expand (columnBorn ψ.a0) (columnBorn ψ.a1)))

theorem matSame_mul {A A' B B' : Mat} (hA : matSame A A') (hB : matSame B B') :
    matSame (matMul A B) (matMul A' B') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact polySame_append
      (polySame.trans (polySame_pmul_left hA.1 B.a00) (polySame_pmul_right hB.1 A'.a00))
      (polySame.trans (polySame_pmul_left hA.2.1 B.a10) (polySame_pmul_right hB.2.2.1 A'.a01))
  · exact polySame_append
      (polySame.trans (polySame_pmul_left hA.1 B.a01) (polySame_pmul_right hB.2.1 A'.a00))
      (polySame.trans (polySame_pmul_left hA.2.1 B.a11) (polySame_pmul_right hB.2.2.2 A'.a01))
  · exact polySame_append
      (polySame.trans (polySame_pmul_left hA.2.2.1 B.a00) (polySame_pmul_right hB.1 A'.a10))
      (polySame.trans (polySame_pmul_left hA.2.2.2 B.a10) (polySame_pmul_right hB.2.2.1 A'.a11))
  · exact polySame_append
      (polySame.trans (polySame_pmul_left hA.2.2.1 B.a01) (polySame_pmul_right hB.2.1 A'.a10))
      (polySame.trans (polySame_pmul_left hA.2.2.2 B.a11) (polySame_pmul_right hB.2.2.2 A'.a11))

theorem purity_matSame {A B : Mat} (h : matSame A B) :
    polySame (purity A) (purity B) := by
  have hsq := matSame_mul h h
  simpa only [purity, matTrace] using polySame_append hsq.1 hsq.2.2.2

/-- Una matrice diagonale ha purezza `p² + q²`. -/
theorem diag_square (p q : Poly) :
    polySame (purity ⟨p, [], [], q⟩) (pmul p p ++ pmul q q) := by
  simp only [purity, matTrace, matMul, pmul_nil, pmul_nil_left, List.append_nil, List.nil_append]
  exact polySame_refl _

/-- Dopo `CNOT` le quattro entrate dello stato ridotto sono `|α|²`, `0`, `0`, `|β|²`. -/
theorem decohered_diag (ψ : Pair) :
    matSame (reduceLeft (applyCNOT (tensorPair ψ ket0)))
      ⟨columnBorn ψ.a0, [], [], columnBorn ψ.a1⟩ := by
  rw [cnot_ket0]
  simp only [reduceLeft, columnBorn_nil, conjP, pmul_nil, pmul_nil_left, List.append_nil,
    List.nil_append]
  exact ⟨polySame_refl _, polySame_refl _, polySame_refl _, polySame_refl _⟩

/-- Dopo `CNOT` la purezza del sistema è `|α|⁴ + |β|⁴`. -/
theorem purity_after (ψ : Pair) :
    polySame (purity (reduceLeft (applyCNOT (tensorPair ψ ket0))))
      (pmul (columnBorn ψ.a0) (columnBorn ψ.a0) ++
        pmul (columnBorn ψ.a1) (columnBorn ψ.a1)) :=
  polySame.trans (purity_matSame (decohered_diag ψ)) (diag_square _ _)

/-- I quattro addendi di `(a + b)²` e di `a² + b² + 2ab` hanno gli stessi coefficienti. -/
theorem polySame_cross_swap (a b c d : Poly) :
    polySame ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (d ++ b)) := by
  intro t
  rw [coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append,
    coeffOf_append]
  calc
    (coeffOf a t + coeffOf b t) + (coeffOf c t + coeffOf d t)
        = (coeffOf a t + coeffOf c t) + (coeffOf b t + coeffOf d t) :=
          Gauss.add_add_add_comm _ _ _ _
    _ = (coeffOf a t + coeffOf c t) + (coeffOf d t + coeffOf b t) := by
          rw [Gauss.add_comm (coeffOf b t) (coeffOf d t)]

/-- `|α|⁴ + |β|⁴ + 2|α|²|β|²` ha i coefficienti di `‖ψ‖⁴`. -/
theorem polySame_decohered_square (ψ : Pair) :
    polySame
      (purity (reduceLeft (applyCNOT (tensorPair ψ ket0))) ++
        (pmul (columnBorn ψ.a0) (columnBorn ψ.a1) ++
          pmul (columnBorn ψ.a0) (columnBorn ψ.a1)))
      (pmul (normPair ψ) (normPair ψ)) := by
  have hpur := purity_after ψ
  have htwo : polySame
      (pmul (columnBorn ψ.a0) (columnBorn ψ.a1) ++
        pmul (columnBorn ψ.a0) (columnBorn ψ.a1))
      (pmul (columnBorn ψ.a0) (columnBorn ψ.a1) ++
        pmul (columnBorn ψ.a1) (columnBorn ψ.a0)) :=
    polySame_append (polySame_refl _)
      (polySame_mul_comm (columnBorn ψ.a0) (columnBorn ψ.a1))
  have hshuffle := polySame_cross_swap
      (pmul (columnBorn ψ.a0) (columnBorn ψ.a0))
      (pmul (columnBorn ψ.a1) (columnBorn ψ.a1))
      (pmul (columnBorn ψ.a0) (columnBorn ψ.a1))
      (pmul (columnBorn ψ.a1) (columnBorn ψ.a0))
  exact polySame.trans (polySame_append hpur htwo)
    (polySame.trans hshuffle
      (polySame.symm (square_expand (columnBorn ψ.a0) (columnBorn ψ.a1))))

theorem psub_neg_swap (p q : Poly) : polySame (psub p q) (pneg (psub q p)) := by
  intro t
  rw [coeff_psub, coeff_pneg, coeff_psub, Gauss.neg_add, Gauss.neg_neg, Gauss.add_comm]

/-- `n² − 1` ha i coefficienti di `(n − 1)(n + 1)`. -/
theorem polySame_square_diff (n : Poly) :
    polySame (pmul (psub n (single 1 Mono.one)) (n ++ single 1 Mono.one))
      (psub (pmul n n) (single 1 Mono.one)) := by
  have hmul := polySame_mul_psub_left n (single 1 Mono.one) (n ++ single 1 Mono.one)
  have hone : pmul (single 1 Mono.one) (n ++ single 1 Mono.one) = n ++ single 1 Mono.one :=
    one_pmul _
  have hdist : polySame (pmul n (n ++ single 1 Mono.one)) (pmul n n ++ n) :=
    polySame.trans (polySame_mul_append_right n n (single 1 Mono.one))
      (fun _ => by rw [pmul_one])
  have happ : polySame
      (psub (pmul n (n ++ single 1 Mono.one))
        (pmul (single 1 Mono.one) (n ++ single 1 Mono.one)))
      (psub (pmul n n ++ n) (n ++ single 1 Mono.one)) :=
    polySame_psub hdist (fun _ => by rw [hone])
  have hsplit := polySame_psub_append (pmul n n) n n (single 1 Mono.one)
  have hcancel : polySame
      (psub (pmul n n) n ++ psub n (single 1 Mono.one))
      (psub (pmul n n) (single 1 Mono.one)) := by
    intro t
    rw [coeffOf_append, coeff_psub, coeff_psub, coeff_psub]
    ext <;> simp <;> grind
  exact polySame.trans hmul (polySame.trans happ (polySame.trans hsplit hcancel))

/-- Se `n − 1` ha i coefficienti di `gA`, allora `1 − n²` ha cofattore `−(n + 1)`. -/
theorem one_sub_square (n : Poly) (hμ : polySame (psub n (single 1 Mono.one)) gA) :
    inIdeal3 (psub (single 1 Mono.one) (pmul n n)) := by
  refine ⟨[], [], pneg (n ++ single 1 Mono.one), ?_⟩
  intro t
  have hdiff := polySame_square_diff n
  have hga : polySame (pmul gA (n ++ single 1 Mono.one))
      (psub (pmul n n) (single 1 Mono.one)) :=
    polySame.trans (polySame.symm (polySame_pmul_left hμ (n ++ single 1 Mono.one))) hdiff
  have hcomm : polySame (pmul gA (n ++ single 1 Mono.one))
      (pmul (n ++ single 1 Mono.one) gA) :=
    polySame_mul_comm gA (n ++ single 1 Mono.one)
  have hneg : polySame (pneg (pmul gA (n ++ single 1 Mono.one)))
      (pmul (pneg (n ++ single 1 Mono.one)) gA) :=
    polySame.trans (polySame_pneg hcomm) (fun _ => by rw [pneg_pmul])
  have htarget : polySame (psub (single 1 Mono.one) (pmul n n))
      (pmul (pneg (n ++ single 1 Mono.one)) gA) :=
    polySame.trans (psub_neg_swap _ _)
      (polySame.trans (polySame_pneg (polySame.symm hga)) hneg)
  rw [htarget t]
  simp [pmul, Universe.Quotient.mul, List.nil_append]

/-- Sulla sfera, `1 − purezza − 2|α|²|β|²` ha cofattore `gA`. -/
theorem purity_sphere :
    inIdeal3 (psub (single 1 Mono.one)
      (purity (reduceLeft (applyCNOT (tensorPair genericPair ket0))) ++
        (pmul (columnBorn genericPair.a0) (columnBorn genericPair.a1) ++
          pmul (columnBorn genericPair.a0) (columnBorn genericPair.a1)))) :=
  inIdeal3_polySame
    (polySame_psub (polySame_refl _) (polySame_decohered_square genericPair))
    (one_sub_square (normPair genericPair) normPair_generic)

/-! ### Valutazione nel punto -/

theorem eval_a00_point : evalAt pointC pointS 1 0 0 evolution.a00 = pointAlpha := by
  rw [evolution_a00_bin, eval_append, eval_single, eval_single]
  simp [pointAlpha, monoVal, powR, c1, s1, nz1, Mono.mul, pointC, pointS,
    Gauss.re_neg, Gauss.im_neg, Gauss.re_i, Gauss.im_i]
  ext <;> simp <;> grind

theorem eval_a10_point : evalAt pointC pointS 1 0 0 evolution.a10 = pointBeta := by
  rw [evolution_a10_bin, eval_append, eval_single, eval_single]
  simp [pointBeta, monoVal, powR, s1, nx1, ny1, Mono.mul, pointC, pointS,
    Gauss.re_neg, Gauss.im_neg, Gauss.re_i, Gauss.im_i]
  ext <;> simp <;> grind

/-- Nel punto la purezza del sistema, dopo `CNOT`, è `337/625`. È minore di `1`. -/
theorem point_purity :
    evalAt pointC pointS 1 0 0
        (purity (reduceLeft (applyCNOT (tensorPair (applyMat evolution ket0) ket0)))) =
      ⟨(337 : Rat) / 625, 0⟩ ∧
      ((337 : Rat) / 625) < 1 := by
  refine ⟨?_, ?_⟩
  · have hket : applyMat evolution ket0 = ⟨evolution.a00, evolution.a10⟩ := by
      simp only [applyMat, ket0, pmul_one, pmul_nil, List.append_nil]
    have hpur := purity_after (applyMat evolution ket0)
    rw [eval_polySame hpur, hket, eval_append, eval_pmul, eval_pmul, columnBorn, columnBorn,
      eval_pmul, eval_pmul, eval_conj, eval_conj, eval_a00_point, eval_a10_point]
    simp [pointAlpha, pointBeta, pointC, pointS, Gauss.conj]
    ext <;> simp <;> grind
  · grind

/-! ### Due osservatori -/

/-- `CNOT` fra il sistema e il primo apparato. Scambia le celle `4↔6` e `5↔7`. -/
def cnot01 (v : Oct) : Oct := ⟨v.a0, v.a1, v.a2, v.a3, v.a6, v.a7, v.a4, v.a5⟩

/-- `CNOT` fra il sistema e il secondo apparato. Scambia le celle `4↔5` e `6↔7`. -/
def cnot02 (v : Oct) : Oct := ⟨v.a0, v.a1, v.a2, v.a3, v.a5, v.a4, v.a7, v.a6⟩

/-- `CNOT` di Wigner sull'amico. Il controllo è il bit medio, il bersaglio il bit basso.

Scambia le celle `2↔3` e `6↔7`. -/
def cnot12 (v : Oct) : Oct := ⟨v.a0, v.a1, v.a3, v.a2, v.a4, v.a5, v.a7, v.a6⟩

/-- `cnot12` è un'involuzione. -/
theorem cnot12_involutive (v : Oct) : cnot12 (cnot12 v) = v := by
  cases v
  rfl

/-- `cnot02 ∘ cnot01` su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩` è `α|000⟩ + β|111⟩`. -/
theorem two_pointers (ψ : Pair) :
    cnot02 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)) =
      ⟨ψ.a0, [], [], [], [], [], [], ψ.a1⟩ := by
  rw [tensor_idle_right]
  simp only [tensorLeft, ket0, cnot01, cnot02, pmul_one, pmul_nil]

/-- I due apparati non sono mai in disaccordo.

Le celle in cui i due bit differiscono stanno fra 1 e 6, e ognuna ha
peso zero. Le celle 0 e 7 portano `bornPair ψ`: o leggono entrambi 0,
o leggono entrambi 1. -/
theorem observers_agree (ψ : Pair) :
    bornOct (cnot02 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0))) =
      ⟨columnBorn ψ.a0, [], [], [], [], [], [], columnBorn ψ.a1⟩ := by
  rw [two_pointers]
  simp only [bornOct, columnBorn_nil]

/-- I due `CNOT` danno lo stesso stato. L'ordine degli apparati non conta. -/
theorem order_irrelevant (ψ : Pair) :
    cnot01 (cnot02 (tensorLeft (tensorPair ψ ket0) ket0)) =
      cnot02 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)) := by
  rw [two_pointers, tensor_idle_right]
  simp only [tensorLeft, ket0, cnot01, cnot02, pmul_one, pmul_nil]

/-- La stessa forma di GHZ, costruita come `tensorRight`. `tensor_assoc` identifica le due ottuple. -/
theorem two_pointers_right (ψ : Pair) :
    cnot02 (cnot01 (tensorRight ψ (tensorPair ket0 ket0))) =
      ⟨ψ.a0, [], [], [], [], [], [], ψ.a1⟩ := by
  rw [← tensor_assoc]
  exact two_pointers ψ

/-- Lo stesso accordo, sulla parentesizzazione destra. -/
theorem observers_agree_right (ψ : Pair) :
    bornOct (cnot02 (cnot01 (tensorRight ψ (tensorPair ket0 ket0)))) =
      ⟨columnBorn ψ.a0, [], [], [], [], [], [], columnBorn ψ.a1⟩ := by
  rw [← tensor_assoc]
  exact observers_agree ψ

/-- Lo stesso ordine irrilevante, sulla parentesizzazione destra. -/
theorem order_irrelevant_right (ψ : Pair) :
    cnot01 (cnot02 (tensorRight ψ (tensorPair ket0 ket0))) =
      cnot02 (cnot01 (tensorRight ψ (tensorPair ket0 ket0))) := by
  rw [← tensor_assoc]
  exact order_irrelevant ψ

/-! ### Wigner legge l'amico -/

/-- `cnot12 ∘ cnot01` su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩` è `α|000⟩ + β|111⟩`.

Wigner, leggendo il puntatore dell'amico, legge il sistema. -/
theorem chain_pointers (ψ : Pair) :
    cnot12 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)) =
      ⟨ψ.a0, [], [], [], [], [], [], ψ.a1⟩ := by
  rw [tensor_idle_right]
  simp only [tensorLeft, ket0, cnot01, cnot12, pmul_one, pmul_nil]

/-- La catena è il fan-out `cnot02 ∘ cnot01`.

Quindi `observers_agree` e `order_irrelevant` valgono sullo stesso stato. -/
theorem chain_is_fanout (ψ : Pair) :
    cnot12 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)) =
      cnot02 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)) := by
  rw [chain_pointers, two_pointers]

/-- Wigner e l'amico non sono mai in disaccordo.

`bornOct` è quello di `observers_agree`: le celle 1–6 hanno peso zero,
e le celle 0 e 7 portano `bornPair ψ`. -/
theorem chain_agree (ψ : Pair) :
    bornOct (cnot12 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0))) =
      ⟨columnBorn ψ.a0, [], [], [], [], [], [], columnBorn ψ.a1⟩ := by
  rw [chain_is_fanout]
  exact observers_agree ψ

/-! ### Disfare l'amico -/

/-- Traccia parziale su amico e Wigner. L'indice è `4 * i + 2 * j + k`.

L'entrata `(i, i')` somma `a · conj(a')` sui due bit tracciati. -/
def reduceSystem (v : Oct) : Mat where
  a00 := columnBorn v.a0 ++ columnBorn v.a1 ++ columnBorn v.a2 ++ columnBorn v.a3
  a01 :=
    pmul v.a0 (conjP v.a4) ++ pmul v.a1 (conjP v.a5) ++
      pmul v.a2 (conjP v.a6) ++ pmul v.a3 (conjP v.a7)
  a10 :=
    pmul v.a4 (conjP v.a0) ++ pmul v.a5 (conjP v.a1) ++
      pmul v.a6 (conjP v.a2) ++ pmul v.a7 (conjP v.a3)
  a11 := columnBorn v.a4 ++ columnBorn v.a5 ++ columnBorn v.a6 ++ columnBorn v.a7

/-- Su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩` il sistema ridotto è `|ψ⟩⟨ψ|`. -/
theorem reduceSystem_product (ψ : Pair) :
    matSame (reduceSystem (tensorLeft (tensorPair ψ ket0) ket0)) (outer ψ) := by
  rw [tensor_idle_right]
  simp only [tensorLeft, ket0, reduceSystem, outer, pmul_one, pmul_nil, columnBorn_nil,
    conjP, List.append_nil]
  exact ⟨polySame_refl _, polySame_refl _, polySame_refl _, polySame_refl _⟩

/-- `cnot01` due volte restituisce `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩`.

La coerenza `α conj(β)` è di nuovo l'antidiagonale del sistema ridotto,
come in `coherence_before`. -/
theorem friend_undone (ψ : Pair) :
    cnot01 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)) =
        tensorLeft (tensorPair ψ ket0) ket0 ∧
      polySame
        (reduceSystem (cnot01 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)))).a01
        (pmul ψ.a0 (conjP ψ.a1)) := by
  have hrestore :
      cnot01 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)) =
        tensorLeft (tensorPair ψ ket0) ket0 := by
    rw [tensor_idle_right]
    simp only [tensorLeft, ket0, cnot01, pmul_one, pmul_nil]
  refine ⟨hrestore, ?_⟩
  rw [hrestore]
  exact (reduceSystem_product ψ).2.1

/-- Dopo `cnot12`, disfare l'amico lascia `α|000⟩ + β|101⟩`.

Le due entrate fuori diagonale di `reduceSystem` sono il polinomio zero
e la diagonale è `bornPair ψ`, come in `decoherence`. -/
theorem copy_irreversible (ψ : Pair) :
    cnot01 (cnot12 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0))) =
        ⟨ψ.a0, [], [], [], [], ψ.a1, [], []⟩ ∧
      polySame
          (reduceSystem (cnot01 (cnot12 (cnot01
            (tensorLeft (tensorPair ψ ket0) ket0))))).a01
          [] ∧
        polySame
            (reduceSystem (cnot01 (cnot12 (cnot01
              (tensorLeft (tensorPair ψ ket0) ket0))))).a10
            [] ∧
          pairSame
              ⟨(reduceSystem (cnot01 (cnot12 (cnot01
                  (tensorLeft (tensorPair ψ ket0) ket0))))).a00,
                (reduceSystem (cnot01 (cnot12 (cnot01
                  (tensorLeft (tensorPair ψ ket0) ket0))))).a11⟩
              (bornPair ψ) := by
  have hv :
      cnot01 (cnot12 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0))) =
        ⟨ψ.a0, [], [], [], [], ψ.a1, [], []⟩ := by
    rw [chain_pointers]
    rfl
  refine ⟨hv, ?_, ?_, ?_⟩
  all_goals
    rw [hv]
    simp only [reduceSystem, bornPair, columnBorn_nil, conjP, pmul_nil, pmul_nil_left,
      List.append_nil, List.nil_append]
  · exact polySame_refl _
  · exact polySame_refl _
  · exact pairSame_refl _

/-- Marginale di Wigner, il bit basso. Somma sui bit di sistema e amico. -/
def marginalWigner (v : Oct) : Pair where
  a0 := columnBorn v.a0 ++ columnBorn v.a2 ++ columnBorn v.a4 ++ columnBorn v.a6
  a1 := columnBorn v.a1 ++ columnBorn v.a3 ++ columnBorn v.a5 ++ columnBorn v.a7

/-- Nello stato `α|000⟩ + β|101⟩` Wigner legge ancora `bornPair ψ`. -/
theorem wigner_keeps_record (ψ : Pair) :
    pairSame
      (marginalWigner
        (cnot01 (cnot12 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)))))
      (bornPair ψ) := by
  rw [(copy_irreversible ψ).1]
  simp only [marginalWigner, bornPair, columnBorn_nil, List.append_nil, List.nil_append]
  exact pairSame_refl _

/-! ### Il punto razionale -/

/-- Nel punto `ψ = Φ|0⟩`, `c = 3/5`, `s = 4/5`, `n = e_x`.

Disfare l'amico restituisce la coerenza `12/25 i` e la purezza `1`.
`eval_purity` porta `Tr(ρ²)` sulle quattro entrate di `|ψ⟩⟨ψ|`. -/
theorem point_undone :
    evalAt pointC pointS 1 0 0
        (reduceSystem (cnot01 (cnot01
          (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0)))).a01 =
      ⟨0, (12 : Rat) / 25⟩ ∧
      evalAt pointC pointS 1 0 0
          (purity (reduceSystem (cnot01 (cnot01
            (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0))))) =
        ⟨1, 0⟩ := by
  have hket : applyMat evolution ket0 = ⟨evolution.a00, evolution.a10⟩ := by
    simp only [applyMat, ket0, pmul_one, pmul_nil, List.append_nil]
  refine ⟨?_, ?_⟩
  · rw [eval_polySame (friend_undone (applyMat evolution ket0)).2, hket]
    rw [eval_pmul, eval_conj, eval_a00_point, eval_a10_point]
    simp only [pointAlpha, pointBeta, pointC, pointS, Gauss.conj]
    ext <;> simp <;> grind
  · have hrestore := (friend_undone (applyMat evolution ket0)).1
    rw [hrestore]
    rw [eval_polySame (purity_matSame (reduceSystem_product (applyMat evolution ket0)))]
    have he00 : evalAt pointC pointS 1 0 0 (outer (applyMat evolution ket0)).a00 =
        pointAlpha * Gauss.conj pointAlpha := by
      rw [hket]
      simp only [outer, columnBorn]
      rw [eval_pmul, eval_conj, eval_a00_point]
    have he11 : evalAt pointC pointS 1 0 0 (outer (applyMat evolution ket0)).a11 =
        pointBeta * Gauss.conj pointBeta := by
      rw [hket]
      simp only [outer, columnBorn]
      rw [eval_pmul, eval_conj, eval_a10_point]
    have he01 : evalAt pointC pointS 1 0 0 (outer (applyMat evolution ket0)).a01 =
        pointAlpha * Gauss.conj pointBeta := by
      rw [hket]
      simp only [outer]
      rw [eval_pmul, eval_conj, eval_a00_point, eval_a10_point]
    have he10 : evalAt pointC pointS 1 0 0 (outer (applyMat evolution ket0)).a10 =
        pointBeta * Gauss.conj pointAlpha := by
      rw [hket]
      simp only [outer]
      rw [eval_pmul, eval_conj, eval_a10_point, eval_a00_point]
    rw [eval_purity, he00, he01, he10, he11]
    simp only [pointAlpha, pointBeta, pointC, pointS, Gauss.conj]
    ext <;> simp <;> grind

/-- Nello stesso punto, dopo la copia, la coerenza è `0` e la purezza è `337/625`.

Wigner legge `9/25` e `16/25`. `eval_purity` espande `Tr(ρ²)`. Il valore
è quello di `point_purity`: la diagonale è la stessa di `decoherence`. -/
theorem point_copied :
    evalAt pointC pointS 1 0 0
        (reduceSystem (cnot01 (cnot12 (cnot01
          (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0))))).a01 = 0 ∧
      evalAt pointC pointS 1 0 0
          (purity (reduceSystem (cnot01 (cnot12 (cnot01
            (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0)))))) =
        ⟨(337 : Rat) / 625, 0⟩ ∧
        evalAt pointC pointS 1 0 0
            (marginalWigner (cnot01 (cnot12 (cnot01
              (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0))))).a0 =
          ⟨(9 : Rat) / 25, 0⟩ ∧
          evalAt pointC pointS 1 0 0
              (marginalWigner (cnot01 (cnot12 (cnot01
                (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0))))).a1 =
            ⟨(16 : Rat) / 25, 0⟩ := by
  let ψ := applyMat evolution ket0
  have hket : ψ = ⟨evolution.a00, evolution.a10⟩ := by
    unfold ψ
    simp only [applyMat, ket0, pmul_one, pmul_nil, List.append_nil]
  let copied :=
    cnot01 (cnot12 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0)))
  have hcopy := copy_irreversible ψ
  have hcells : matSame (reduceSystem copied)
      ⟨columnBorn ψ.a0, [], [], columnBorn ψ.a1⟩ :=
    ⟨hcopy.2.2.2.1, hcopy.2.1, hcopy.2.2.1, hcopy.2.2.2.2⟩
  have hpur : polySame (purity (reduceSystem copied))
      (purity (reduceLeft (applyCNOT (tensorPair ψ ket0)))) :=
    polySame.trans (purity_matSame hcells)
      (polySame.symm (purity_matSame (decohered_diag ψ)))
  have he00 : evalAt pointC pointS 1 0 0 (reduceSystem copied).a00 =
      pointAlpha * Gauss.conj pointAlpha := by
    rw [eval_polySame hcells.1, hket]
    simp only [columnBorn]
    rw [eval_pmul, eval_conj, eval_a00_point]
  have he01 : evalAt pointC pointS 1 0 0 (reduceSystem copied).a01 = 0 := by
    rw [eval_polySame hcells.2.1]
    rfl
  have he10 : evalAt pointC pointS 1 0 0 (reduceSystem copied).a10 = 0 := by
    rw [eval_polySame hcells.2.2.1]
    rfl
  have he11 : evalAt pointC pointS 1 0 0 (reduceSystem copied).a11 =
      pointBeta * Gauss.conj pointBeta := by
    rw [eval_polySame hcells.2.2.2, hket]
    simp only [columnBorn]
    rw [eval_pmul, eval_conj, eval_a10_point]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eval_polySame hcells.2.1]
    rfl
  · rw [eval_purity, he00, he01, he10, he11]
    have hvalue := point_purity.1
    rw [(eval_polySame hpur pointC pointS 1 0 0).symm, eval_purity, he00, he01, he10,
      he11] at hvalue
    exact hvalue
  · rw [eval_polySame (wigner_keeps_record ψ).1, hket]
    simp only [bornPair, columnBorn]
    rw [eval_pmul, eval_conj, eval_a00_point]
    simp only [pointAlpha, pointC, Gauss.conj]
    ext <;> simp <;> grind
  · rw [eval_polySame (wigner_keeps_record ψ).2, hket]
    simp only [bornPair, columnBorn]
    rw [eval_pmul, eval_conj, eval_a10_point]
    simp only [pointBeta, pointS, Gauss.conj]
    ext <;> simp <;> grind

/-! ### L'apparato non segnala -/

/-- `I ⊗ U` non cambia `P(0)` del sistema, per ogni stato di due qubit.

È la prima componente di `no_signalling_at` sul qubit `0`, con il
unitario sul qubit `1`. `applyAt 1` è `applyIU` e `marginalAt 0` è
`marginalLeft`. -/
theorem no_signalling_any_0 (v : Quad) :
    inIdeal
      (psub (marginalLeft (applyIU evolution v)).a0 (marginalLeft v).a0) :=
  (no_signalling_at (0 : Fin 2) 1 (by decide) (ofQuad v)).1

/-- `I ⊗ U` non cambia `P(1)` del sistema, per ogni stato di due qubit.

È la seconda componente dello stesso `no_signalling_at`. -/
theorem no_signalling_any_1 (v : Quad) :
    inIdeal
      (psub (marginalLeft (applyIU evolution v)).a1 (marginalLeft v).a1) :=
  (no_signalling_at (0 : Fin 2) 1 (by decide) (ofQuad v)).2

/-- `I ⊗ U` sull'apparato non cambia `P(0)` del sistema accoppiato da `CNOT`.

È il caso `v = CNOT(|ψ⟩ ⊗ |0⟩)` di `no_signalling_any_0`. -/
theorem no_signalling_0 (ψ : Pair) :
    inIdeal
      (psub (marginalLeft (applyIU evolution (applyCNOT (tensorPair ψ ket0)))).a0
        (marginalLeft (applyCNOT (tensorPair ψ ket0))).a0) :=
  no_signalling_any_0 _

/-- `I ⊗ U` sull'apparato non cambia `P(1)` del sistema accoppiato da `CNOT`.

È il caso `v = CNOT(|ψ⟩ ⊗ |0⟩)` di `no_signalling_any_1`. -/
theorem no_signalling_1 (ψ : Pair) :
    inIdeal
      (psub (marginalLeft (applyIU evolution (applyCNOT (tensorPair ψ ket0)))).a1
        (marginalLeft (applyCNOT (tensorPair ψ ket0))).a1) :=
  no_signalling_any_1 _

/-- `I ⊗ U` non cambia `P(0)` di `genericQuad`.

Le quattro celle sono piene: il caso è `no_signalling_any_0`. -/
theorem no_signalling_gen_0 :
    inIdeal
      (psub (marginalLeft (applyIU evolution genericQuad)).a0
        (marginalLeft genericQuad).a0) :=
  no_signalling_any_0 genericQuad

/-- `I ⊗ U` non cambia `P(1)` di `genericQuad`.

Stesso ideale di `no_signalling_gen_0`. Il caso è `no_signalling_any_1`. -/
theorem no_signalling_gen_1 :
    inIdeal
      (psub (marginalLeft (applyIU evolution genericQuad)).a1
        (marginalLeft genericQuad).a1) :=
  no_signalling_any_1 genericQuad

/-! ### Tre parti, nessun segnale -/

/-- `(I ⊗ I ⊗ U)` sul bit basso, il qubit di Wigner.

L'indice è `4 * i + 2 * j + k`. Per ogni `(i, j)` le celle `k = 0` e
`k = 1` sono un qubit. -/
def applyIIU (U : Mat) (v : Oct) : Oct where
  a0 := pmul U.a00 v.a0 ++ pmul U.a01 v.a1
  a1 := pmul U.a10 v.a0 ++ pmul U.a11 v.a1
  a2 := pmul U.a00 v.a2 ++ pmul U.a01 v.a3
  a3 := pmul U.a10 v.a2 ++ pmul U.a11 v.a3
  a4 := pmul U.a00 v.a4 ++ pmul U.a01 v.a5
  a5 := pmul U.a10 v.a4 ++ pmul U.a11 v.a5
  a6 := pmul U.a00 v.a6 ++ pmul U.a01 v.a7
  a7 := pmul U.a10 v.a6 ++ pmul U.a11 v.a7

/-- `(I ⊗ U ⊗ I)` sul bit medio, il qubit dell'amico.

Per ogni `(i, k)` le celle `j = 0` e `j = 1` sono un qubit. -/
def applyIUI (U : Mat) (v : Oct) : Oct where
  a0 := pmul U.a00 v.a0 ++ pmul U.a01 v.a2
  a1 := pmul U.a00 v.a1 ++ pmul U.a01 v.a3
  a2 := pmul U.a10 v.a0 ++ pmul U.a11 v.a2
  a3 := pmul U.a10 v.a1 ++ pmul U.a11 v.a3
  a4 := pmul U.a00 v.a4 ++ pmul U.a01 v.a6
  a5 := pmul U.a00 v.a5 ++ pmul U.a01 v.a7
  a6 := pmul U.a10 v.a4 ++ pmul U.a11 v.a6
  a7 := pmul U.a10 v.a5 ++ pmul U.a11 v.a7

/-- `applyAt 1` su tre qubit è `I ⊗ U ⊗ I`. -/
theorem applyAt_iui (U : Mat) (v : Oct) :
    toOct (applyAt (1 : Fin 3) U (ofOct v)) = applyIUI U v := rfl

/-- `applyAt 2` su tre qubit è `I ⊗ I ⊗ U`. -/
theorem applyAt_iiu (U : Mat) (v : Oct) :
    toOct (applyAt (2 : Fin 3) U (ofOct v)) = applyIIU U v := rfl

/-- La diagonale di `reduceSystem` ha i coefficienti di `marginalAt 0`.

`reduceSystem` associa a sinistra. `normQ` associa a coppie. -/
theorem reduceSystem_marginal (v : Oct) :
    polySame (reduceSystem v).a00 (marginalAt (0 : Fin 3) (ofOct v)).a0 ∧
      polySame (reduceSystem v).a11 (marginalAt (0 : Fin 3) (ofOct v)).a1 := by
  have hmarg : marginalAt (0 : Fin 3) (ofOct v) =
      ⟨(columnBorn v.a0 ++ columnBorn v.a1) ++ (columnBorn v.a2 ++ columnBorn v.a3),
        (columnBorn v.a4 ++ columnBorn v.a5) ++ (columnBorn v.a6 ++ columnBorn v.a7)⟩ :=
    rfl
  simp only [hmarg, reduceSystem]
  exact ⟨polySame_append_assoc (columnBorn v.a0 ++ columnBorn v.a1)
      (columnBorn v.a2) (columnBorn v.a3),
    polySame_append_assoc (columnBorn v.a4 ++ columnBorn v.a5)
      (columnBorn v.a6) (columnBorn v.a7)⟩

/-- `I ⊗ I ⊗ U` non cambia i pesi di Born del sistema, per ogni `Oct`.

È `no_signalling_at` fra il qubit `0` e il qubit `2`. La diagonale di
`reduceSystem` ha i coefficienti di `marginalAt 0`. -/
theorem no_signalling_wigner (v : Oct) :
    inIdeal
        (psub (reduceSystem (applyIIU evolution v)).a00 (reduceSystem v).a00) ∧
      inIdeal
        (psub (reduceSystem (applyIIU evolution v)).a11 (reduceSystem v).a11) := by
  have h := no_signalling_at (0 : Fin 3) (2 : Fin 3) (by decide) (ofOct v)
  have hU := reduceSystem_marginal (applyIIU evolution v)
  have hB := reduceSystem_marginal v
  exact ⟨inIdeal_polySame (polySame_psub hU.1 hB.1) h.1,
    inIdeal_polySame (polySame_psub hU.2 hB.2) h.2⟩

/-- `I ⊗ U ⊗ I` non cambia i pesi di Born del sistema, per ogni `Oct`.

Stesso ideale di `no_signalling_wigner`. Il unitario sta sul qubit `1`. -/
theorem no_signalling_friend (v : Oct) :
    inIdeal
        (psub (reduceSystem (applyIUI evolution v)).a00 (reduceSystem v).a00) ∧
      inIdeal
        (psub (reduceSystem (applyIUI evolution v)).a11 (reduceSystem v).a11) := by
  have h := no_signalling_at (0 : Fin 3) (1 : Fin 3) (by decide) (ofOct v)
  have hU := reduceSystem_marginal (applyIUI evolution v)
  have hB := reduceSystem_marginal v
  exact ⟨inIdeal_polySame (polySame_psub hU.1 hB.1) h.1,
    inIdeal_polySame (polySame_psub hU.2 hB.2) h.2⟩

end Universe.Observer
