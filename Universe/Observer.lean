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
`337/625`.

Due apparati. `cnot01` e `cnot02` agiscono sul bit medio e sul bit basso.
Su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩` entrambi gli ordini danno `α|000⟩ + β|111⟩`. I pesi
di Born delle celle 1–6 sono il polinomio zero: i due apparati non sono
mai in disaccordo. `tensor_assoc` porta gli stessi fatti sulla
parentesizzazione destra. Tutto sta nell'anello libero.

`I ⊗ U` sull'apparato, dopo `CNOT` con `|0⟩`, non cambia il marginale
del sistema. La differenza sta in `(gC, gN)`: i cofattori di `δ`
moltiplicati per `|α|²` e per `|β|²`.
-/
import Universe.Composition
import Universe.Epistemology
import Universe.Evaluation
import Universe.Qubit

namespace Universe.Observer

open Universe.Ring
open Universe.Quotient hiding mul
open Universe.Dynamics
open Universe.Epistemology
open Universe.Evaluation
open Universe.Composition
open Universe.Qubit

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

/-- `|ψ⟩⟨ψ|`. -/
def outer (ψ : Pair) : Mat where
  a00 := columnBorn ψ.a0
  a01 := pmul ψ.a0 (conjP ψ.a1)
  a10 := pmul ψ.a1 (conjP ψ.a0)
  a11 := columnBorn ψ.a1

/-- Un fattore di `|φ|²` esce dal prodotto `α φ · conj(β φ)`. -/
theorem coherence_scale (p y x : Poly) :
    polySame (pmul (pmul p x) (conjP (pmul y x)))
      (pmul (columnBorn x) (pmul p (conjP y))) := by
  rw [conj_pmul]
  exact polySame.trans (polySame_assoc_comm p x (conjP y) (conjP x))
    (polySame_mul_comm (pmul p (conjP y)) (columnBorn x))

/-- La riga fuori diagonale di un prodotto è `‖φ‖² · α conj(β)`. -/
theorem coherence_row (p y x0 x1 : Poly) :
    polySame
      (pmul (pmul p x0) (conjP (pmul y x0)) ++ pmul (pmul p x1) (conjP (pmul y x1)))
      (pmul (columnBorn x0 ++ columnBorn x1) (pmul p (conjP y))) :=
  polySame.trans (polySame_append (coherence_scale p y x0) (coherence_scale p y x1))
    (fun t => by rw [pmul_append_left])

/-- Senza interazione il sistema resta puro, a meno di `‖φ‖²`. -/
theorem reduce_product (ψ φ : Pair) :
    matSame (reduceLeft (tensorPair ψ φ)) (matScale (normPair φ) (outer ψ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [reduceLeft, tensorPair, matScale, outer, normPair] using
      marginal_scale_row ψ.a0 φ.a0 φ.a1
  · simpa only [reduceLeft, tensorPair, matScale, outer, normPair] using
      coherence_row ψ.a0 ψ.a1 φ.a0 φ.a1
  · simpa only [reduceLeft, tensorPair, matScale, outer, normPair] using
      coherence_row ψ.a1 ψ.a0 φ.a0 φ.a1
  · simpa only [reduceLeft, tensorPair, matScale, outer, normPair] using
      marginal_scale_row ψ.a1 φ.a0 φ.a1

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

/-! ### L'apparato non segnala -/

/-- `|u₀ α|² + |u₁ α|² − |α|²` ha i coefficienti di `|α|² · (|u₀|² + |u₁|² − 1)`.

L'ordine del modulo è `z · conj(z)`. L'identità sta nell'anello libero. -/
theorem born_column_defect (u0 u1 α : Poly) :
    polySame
      (psub (columnBorn (pmul u0 α) ++ columnBorn (pmul u1 α)) (columnBorn α))
      (pmul (columnBorn α)
        (psub (columnBorn u0 ++ columnBorn u1) (single 1 Mono.one))) := by
  have hsum :
      polySame (columnBorn (pmul u0 α) ++ columnBorn (pmul u1 α))
        (pmul (columnBorn α) (columnBorn u0) ++ pmul (columnBorn α) (columnBorn u1)) :=
    polySame_append (columnBorn_pmul u0 α) (columnBorn_pmul u1 α)
  have hdist :
      polySame (pmul (columnBorn α) (columnBorn u0 ++ columnBorn u1))
        (pmul (columnBorn α) (columnBorn u0) ++ pmul (columnBorn α) (columnBorn u1)) :=
    polySame_mul_append_right (columnBorn α) (columnBorn u0) (columnBorn u1)
  have hscaled :
      polySame (columnBorn (pmul u0 α) ++ columnBorn (pmul u1 α))
        (pmul (columnBorn α) (columnBorn u0 ++ columnBorn u1)) :=
    polySame.trans hsum (polySame.symm hdist)
  have hone : polySame (columnBorn α) (pmul (columnBorn α) (single 1 Mono.one)) := by
    rw [pmul_one]
    exact polySame_refl _
  exact polySame.trans (polySame_psub hscaled hone)
    (polySame.symm (polySame_mul_psub_right (columnBorn α)
      (columnBorn u0 ++ columnBorn u1) (single 1 Mono.one)))

/-- La prima colonna di `U` ha norma `1` modulo `δ`, nell'ordine `z · conj(z)`. -/
theorem evolution_column_00 :
    polySame
      (psub (columnBorn evolution.a00 ++ columnBorn evolution.a10) (single 1 Mono.one))
      unitaryDefect := by
  refine polySame.trans ?_ evolution_unitary_00
  refine polySame_psub ?_ (polySame_refl _)
  rw [uu_a00]
  exact polySame_append (columnBorn_comm evolution.a00) (columnBorn_comm evolution.a10)

/-- La seconda colonna di `U` ha norma `1` modulo `δ`, nello stesso ordine. -/
theorem evolution_column_11 :
    polySame
      (psub (columnBorn evolution.a01 ++ columnBorn evolution.a11) (single 1 Mono.one))
      unitaryDefect := by
  have h11 :
      (matMul (matDagger evolution) evolution).a11 =
        pmul (conjP evolution.a01) evolution.a01 ++
          pmul (conjP evolution.a11) evolution.a11 := rfl
  refine polySame.trans ?_ evolution_unitary_11
  refine polySame_psub ?_ (polySame_refl _)
  rw [h11]
  exact polySame_append (columnBorn_comm evolution.a01) (columnBorn_comm evolution.a11)

/-- `I ⊗ U` sull'apparato non cambia `P(0)` del sistema.

`w` è `CNOT(|ψ⟩ ⊗ |0⟩)`. La differenza dei marginali sinistri sta in
`(gC, gN)`: i cofattori sono quelli di `δ`, moltiplicati a sinistra per `|α|²`. -/
theorem no_signalling_0 (ψ : Pair) :
    inIdeal
      (psub (marginalLeft (applyIU evolution (applyCNOT (tensorPair ψ ket0)))).a0
        (marginalLeft (applyCNOT (tensorPair ψ ket0))).a0) := by
  have hstate : applyCNOT (tensorPair ψ ket0) = ⟨ψ.a0, [], [], ψ.a1⟩ := cnot_ket0 ψ
  rw [hstate]
  have hiu :
      applyIU evolution ⟨ψ.a0, [], [], ψ.a1⟩ =
        ⟨pmul evolution.a00 ψ.a0, pmul evolution.a10 ψ.a0,
          pmul evolution.a01 ψ.a1, pmul evolution.a11 ψ.a1⟩ := by
    simp only [applyIU, pmul_nil, List.append_nil, List.nil_append]
  rw [hiu]
  simp only [marginalLeft, columnBorn_nil, List.append_nil, List.nil_append]
  exact inIdeal_polySame (born_column_defect evolution.a00 evolution.a10 ψ.a0)
    (inIdeal_mul_left (columnBorn ψ.a0)
      (inIdeal_polySame evolution_column_00 unitary_ideal))

/-- `I ⊗ U` sull'apparato non cambia `P(1)` del sistema.

Stesso ideale di `no_signalling_0`. Il cofattore sinistro è `|β|²`. -/
theorem no_signalling_1 (ψ : Pair) :
    inIdeal
      (psub (marginalLeft (applyIU evolution (applyCNOT (tensorPair ψ ket0)))).a1
        (marginalLeft (applyCNOT (tensorPair ψ ket0))).a1) := by
  have hstate : applyCNOT (tensorPair ψ ket0) = ⟨ψ.a0, [], [], ψ.a1⟩ := cnot_ket0 ψ
  rw [hstate]
  have hiu :
      applyIU evolution ⟨ψ.a0, [], [], ψ.a1⟩ =
        ⟨pmul evolution.a00 ψ.a0, pmul evolution.a10 ψ.a0,
          pmul evolution.a01 ψ.a1, pmul evolution.a11 ψ.a1⟩ := by
    simp only [applyIU, pmul_nil, List.append_nil, List.nil_append]
  rw [hiu]
  simp only [marginalLeft, columnBorn_nil, List.append_nil, List.nil_append]
  exact inIdeal_polySame (born_column_defect evolution.a01 evolution.a11 ψ.a1)
    (inIdeal_mul_left (columnBorn ψ.a1)
      (inIdeal_polySame evolution_column_11 unitary_ideal))

end Universe.Observer
