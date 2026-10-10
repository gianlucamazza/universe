/-
CNOT e il primo stato entangled.

`applyCNOT` scambia `|10⟩` e `|11⟩`. Su `|ψ⟩ ⊗ |0⟩` resta `α|00⟩ + β|11⟩`.
`quadDet` è zero su ogni prodotto, nell'anello libero. Nel punto
`c = 3/5`, `s = 4/5`, `n = e_x` il determinante di `CNOT(Φ|0⟩ ⊗ |0⟩)`
è `−12/25 i`, quindi quello stato non è un prodotto.
-/
import Universe.Composition
import Universe.Epistemology
import Universe.Qubit

namespace Universe.Observer

open Universe.Ring
open Universe.Quotient hiding mul
open Universe.Dynamics
open Universe.Epistemology
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
  ext <;> simp [pointAlpha, monoVal, powR, c1, Mono.one, pointC, pointS, Gauss.re_one,
    Gauss.im_one] <;> grind

theorem point_beta :
    evalAt pointC pointS 1 0 0 (specPoly keepX evolution.a10) = pointBeta := by
  rw [specX_a10, eval_single]
  ext <;> simp [pointBeta, monoVal, powR, s1, Mono.one, pointC, pointS, Gauss.re_neg,
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
  simp [specPoly, keepX, single, c1, s1, nx1, ny1, nz1, Mono.mul, Mono.one, evalAt,
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

end Universe.Observer
