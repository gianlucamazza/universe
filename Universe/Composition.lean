/-
Composizione di due sistemi a due ampiezze.

L'indice di `|i⟩ ⊗ |k⟩` è `right * i + k`, la stessa formula di `tensor_index`.
`ground_tensor`: `|0⟩ ⊗ |0⟩` ha ampiezza `1` nella cella `0` e `0` altrove.
`kronecker_ui_gen` è `(U ⊗ I)(|ψ⟩ ⊗ |φ⟩) = (U|ψ⟩) ⊗ |φ⟩` per ogni secondo
fattore. `kronecker_ui` è il caso `|φ⟩ = |0⟩`. Il marginale sinistro ha i
coefficienti di `‖φ‖² · P(U|ψ⟩)`. `kronecker_iu_gen` scambia i fattori, nel
senso di `polySame`. Sul fattore generico, togliere `‖φ‖²` chiede `gA`.
-/
import Universe.Epistemology
import Universe.Ontology
import Universe.Qubit

namespace Universe.Composition

open Universe.Ring
open Universe.Quotient hiding mul
open Universe.Dynamics
open Universe.Epistemology

def tensorIndex (i k right : Nat) : Nat := right * i + k

theorem tensorIndex_cells :
    tensorIndex 0 0 2 = 0 ∧ tensorIndex 0 1 2 = 1 ∧
      tensorIndex 1 0 2 = 2 ∧ tensorIndex 1 1 2 = 3 := by
  decide

@[ext]
structure Pair where
  a0 : Poly
  a1 : Poly

@[ext]
structure Quad where
  a0 : Poly
  a1 : Poly
  a2 : Poly
  a3 : Poly

/-- Prodotto `|i⟩ ⊗ |k⟩` con indice `2 * i + k`. -/
def tensorPair (left right : Pair) : Quad where
  a0 := pmul left.a0 right.a0
  a1 := pmul left.a0 right.a1
  a2 := pmul left.a1 right.a0
  a3 := pmul left.a1 right.a1

/-- `|0⟩`, ampiezze `1` e `0`. -/
def ket0 : Pair := ⟨single (1 : Gauss) Mono.one, []⟩

theorem mono_one_mul : Mono.one.mul Mono.one = Mono.one := by
  ext <;> rfl

theorem ground_tensor : tensorPair ket0 ket0 = ⟨single (1 : Gauss) Mono.one, [], [], []⟩ := by
  ext
  · rw [tensorPair, ket0, pmul_single_single, Gauss.mul_one, mono_one_mul, List.append_nil]
  · rw [tensorPair, ket0, pmul_nil]
  · rw [tensorPair, ket0]
    rfl
  · rw [tensorPair, ket0]
    rfl

/-- `|ψ⟩` applicato a una matrice `2×2`. -/
def applyMat (U : Mat) (ψ : Pair) : Pair where
  a0 := pmul U.a00 ψ.a0 ++ pmul U.a01 ψ.a1
  a1 := pmul U.a10 ψ.a0 ++ pmul U.a11 ψ.a1

/-- `(U ⊗ I)` sulla codifica `2 * i + k`. Il fattore `I` vale `1` sulla diagonale. -/
def applyUI (U : Mat) (v : Quad) : Quad where
  a0 := pmul U.a00 v.a0 ++ pmul U.a01 v.a2
  a1 := pmul U.a00 v.a1 ++ pmul U.a01 v.a3
  a2 := pmul U.a10 v.a0 ++ pmul U.a11 v.a2
  a3 := pmul U.a10 v.a1 ++ pmul U.a11 v.a3

/-- `(I ⊗ U)` sulla stessa codifica. -/
def applyIU (U : Mat) (v : Quad) : Quad where
  a0 := pmul U.a00 v.a0 ++ pmul U.a01 v.a1
  a1 := pmul U.a10 v.a0 ++ pmul U.a11 v.a1
  a2 := pmul U.a00 v.a2 ++ pmul U.a01 v.a3
  a3 := pmul U.a10 v.a2 ++ pmul U.a11 v.a3

theorem tensor_idle_right (ψ : Pair) : tensorPair ψ ket0 = ⟨ψ.a0, [], ψ.a1, []⟩ := by
  simp only [tensorPair, ket0]
  rw [pmul_one, pmul_nil, pmul_one, pmul_nil]

theorem pmul_nil_left (q : Poly) : pmul [] q = [] := by
  simp [pmul, Universe.Quotient.mul]

theorem tensor_idle_left (ψ : Pair) : tensorPair ket0 ψ = ⟨ψ.a0, ψ.a1, [], []⟩ := by
  simp only [tensorPair, ket0]
  rw [one_pmul, one_pmul, pmul_nil_left, pmul_nil_left]

theorem kronecker_ui (U : Mat) (ψ : Pair) :
    applyUI U (tensorPair ψ ket0) = tensorPair (applyMat U ψ) ket0 := by
  rw [tensor_idle_right ψ, tensor_idle_right (applyMat U ψ)]
  simp only [applyUI, applyMat, pmul_nil, List.nil_append]

theorem kronecker_iu (U : Mat) (ψ : Pair) :
    applyIU U (tensorPair ket0 ψ) = tensorPair ket0 (applyMat U ψ) := by
  rw [tensor_idle_left ψ, tensor_idle_left (applyMat U ψ)]
  simp only [applyIU, applyMat, pmul_nil, List.nil_append]

def bornPair (ψ : Pair) : Pair where
  a0 := columnBorn ψ.a0
  a1 := columnBorn ψ.a1

/-- Fattore sinistro: somma sull'indice destro. -/
def marginalLeft (v : Quad) : Pair where
  a0 := columnBorn v.a0 ++ columnBorn v.a1
  a1 := columnBorn v.a2 ++ columnBorn v.a3

/-- Fattore destro: somma sull'indice sinistro. -/
def marginalRight (v : Quad) : Pair where
  a0 := columnBorn v.a0 ++ columnBorn v.a2
  a1 := columnBorn v.a1 ++ columnBorn v.a3

theorem columnBorn_nil : columnBorn [] = [] := by
  simp [columnBorn, pmul, Universe.Quotient.mul]

theorem marginal_ui (U : Mat) (ψ : Pair) :
    marginalLeft (applyUI U (tensorPair ψ ket0)) = bornPair (applyMat U ψ) := by
  rw [kronecker_ui, tensor_idle_right]
  simp only [marginalLeft, bornPair, columnBorn_nil, List.append_nil]

theorem marginal_iu (U : Mat) (ψ : Pair) :
    marginalRight (applyIU U (tensorPair ket0 ψ)) = bornPair (applyMat U ψ) := by
  rw [kronecker_iu, tensor_idle_left]
  simp only [marginalRight, bornPair, columnBorn_nil, List.append_nil]

/-! ### Secondo fattore arbitrario -/

/-- `(U ⊗ I)(|ψ⟩ ⊗ |φ⟩) = (U|ψ⟩) ⊗ |φ⟩`, per ogni matrice e ogni coppia. -/
theorem kronecker_ui_gen (U : Mat) (ψ φ : Pair) :
    applyUI U (tensorPair ψ φ) = tensorPair (applyMat U ψ) φ := by
  simp only [applyUI, tensorPair, applyMat]
  rw [pmul_append_left, pmul_append_left, pmul_append_left, pmul_append_left]
  rw [pmul_assoc, pmul_assoc, pmul_assoc, pmul_assoc, pmul_assoc, pmul_assoc,
    pmul_assoc, pmul_assoc]

def quadSame (v w : Quad) : Prop :=
  polySame v.a0 w.a0 ∧ polySame v.a1 w.a1 ∧ polySame v.a2 w.a2 ∧ polySame v.a3 w.a3

def pairSame (ψ φ : Pair) : Prop :=
  polySame ψ.a0 φ.a0 ∧ polySame ψ.a1 φ.a1

theorem pairSame.trans {a b c : Pair} (hab : pairSame a b) (hbc : pairSame b c) :
    pairSame a c :=
  ⟨polySame.trans hab.1 hbc.1, polySame.trans hab.2 hbc.2⟩

/-- Il fattore destro di `(p · x)` attraversa `p`. -/
theorem slide_right (a p x : Poly) :
    polySame (pmul a (pmul p x)) (pmul p (pmul a x)) :=
  polySame.trans (polySame.symm (polySame_pmul_assoc a p x))
    (polySame.trans (polySame_pmul_left (polySame_mul_comm a p) x)
      (polySame_pmul_assoc p a x))

theorem iu_row (a b p x y : Poly) :
    polySame (pmul a (pmul p x) ++ pmul b (pmul p y))
      (pmul p (pmul a x ++ pmul b y)) :=
  polySame.trans (polySame_append (slide_right a p x) (slide_right b p y))
    (polySame.symm (polySame_mul_append_right p (pmul a x) (pmul b y)))

/-- `(I ⊗ U)(|ψ⟩ ⊗ |φ⟩)` e `|ψ⟩ ⊗ (U|φ⟩)` hanno gli stessi coefficienti. -/
theorem kronecker_iu_gen (U : Mat) (ψ φ : Pair) :
    quadSame (applyIU U (tensorPair ψ φ)) (tensorPair ψ (applyMat U φ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [applyIU, tensorPair, applyMat] using iu_row U.a00 U.a01 ψ.a0 φ.a0 φ.a1
  · simpa only [applyIU, tensorPair, applyMat] using iu_row U.a10 U.a11 ψ.a0 φ.a0 φ.a1
  · simpa only [applyIU, tensorPair, applyMat] using iu_row U.a00 U.a01 ψ.a1 φ.a0 φ.a1
  · simpa only [applyIU, tensorPair, applyMat] using iu_row U.a10 U.a11 ψ.a1 φ.a0 φ.a1

/-- `|γ|²` di un prodotto è `|x|² · |p|²`. -/
theorem columnBorn_pmul (p x : Poly) :
    polySame (columnBorn (pmul p x)) (pmul (columnBorn x) (columnBorn p)) :=
  polySame.trans (align_ket p p x x)
    (polySame.trans
      (polySame_pmul_right (polySame_pmul_left (polySame_mul_comm (conjP p) p) x) (conjP x))
      (polySame.trans
        (polySame_pmul_right (polySame_mul_comm (pmul p (conjP p)) x) (conjP x))
        (polySame.trans
          (polySame.symm (polySame_pmul_assoc (conjP x) x (pmul p (conjP p))))
          (polySame_pmul_left (polySame_mul_comm (conjP x) x) (pmul p (conjP p))))))

theorem marginal_scale_row (p x y : Poly) :
    polySame (columnBorn (pmul p x) ++ columnBorn (pmul p y))
      (pmul (columnBorn x ++ columnBorn y) (columnBorn p)) := by
  intro t
  rw [pmul_append_left (columnBorn x) (columnBorn y) (columnBorn p)]
  exact polySame_append (columnBorn_pmul p x) (columnBorn_pmul p y) t

theorem marginal_scale_col (x p q : Poly) :
    polySame (columnBorn (pmul p x) ++ columnBorn (pmul q x))
      (pmul (columnBorn x) (columnBorn p ++ columnBorn q)) :=
  polySame.trans (polySame_append (columnBorn_pmul p x) (columnBorn_pmul q x))
    (polySame.symm (polySame_mul_append_right (columnBorn x) (columnBorn p) (columnBorn q)))

/-- `‖φ‖²` nell'ordine `z · conj(z)`. -/
def normPair (φ : Pair) : Poly := columnBorn φ.a0 ++ columnBorn φ.a1

def scalePair (μ : Poly) (ψ : Pair) : Pair where
  a0 := pmul μ ψ.a0
  a1 := pmul μ ψ.a1

/-- Il marginale sinistro ha i coefficienti di `‖φ‖² · Pᵢ(U|ψ⟩)`. -/
theorem marginal_left_gen (U : Mat) (ψ φ : Pair) :
    pairSame (marginalLeft (applyUI U (tensorPair ψ φ)))
      (scalePair (normPair φ) (bornPair (applyMat U ψ))) := by
  rw [kronecker_ui_gen]
  refine ⟨?_, ?_⟩
  · simpa only [marginalLeft, tensorPair, scalePair, bornPair, normPair] using
      marginal_scale_row (applyMat U ψ).a0 φ.a0 φ.a1
  · simpa only [marginalLeft, tensorPair, scalePair, bornPair, normPair] using
      marginal_scale_row (applyMat U ψ).a1 φ.a0 φ.a1

theorem polySame_conj {p q : Poly} (h : polySame p q) : polySame (conjP p) (conjP q) := by
  intro t
  rw [coeff_conj, coeff_conj, h t]

theorem polySame_columnBorn {p q : Poly} (h : polySame p q) :
    polySame (columnBorn p) (columnBorn q) :=
  polySame.trans (polySame_pmul_left h (conjP p))
    (polySame_pmul_right (polySame_conj h) q)

theorem pairSame_marginalRight {v w : Quad} (h : quadSame v w) :
    pairSame (marginalRight v) (marginalRight w) :=
  ⟨polySame_append (polySame_columnBorn h.1) (polySame_columnBorn h.2.2.1),
    polySame_append (polySame_columnBorn h.2.1) (polySame_columnBorn h.2.2.2)⟩

theorem marginal_right_tensor (ψ ρ : Pair) :
    pairSame (marginalRight (tensorPair ψ ρ)) (scalePair (normPair ψ) (bornPair ρ)) := by
  refine ⟨?_, ?_⟩
  · simpa only [marginalRight, tensorPair, scalePair, bornPair, normPair] using
      polySame.trans (marginal_scale_col ρ.a0 ψ.a0 ψ.a1)
        (polySame_mul_comm (columnBorn ρ.a0) (normPair ψ))
  · simpa only [marginalRight, tensorPair, scalePair, bornPair, normPair] using
      polySame.trans (marginal_scale_col ρ.a1 ψ.a0 ψ.a1)
        (polySame_mul_comm (columnBorn ρ.a1) (normPair ψ))

/-- Il marginale destro ha i coefficienti di `‖ψ‖² · Pᵢ(U|φ⟩)`. -/
theorem marginal_right_gen (U : Mat) (ψ φ : Pair) :
    pairSame (marginalRight (applyIU U (tensorPair ψ φ)))
      (scalePair (normPair ψ) (bornPair (applyMat U φ))) :=
  pairSame.trans (pairSame_marginalRight (kronecker_iu_gen U ψ φ))
    (marginal_right_tensor ψ (applyMat U φ))

theorem normPair_ket0 : polySame (normPair ket0) (single (1 : Gauss) Mono.one) := by
  have hone : columnBorn (single (1 : Gauss) Mono.one) = single 1 Mono.one := by
    have hc : conjP (single (1 : Gauss) Mono.one) = single 1 Mono.one := by
      simp [conjP, single, conj_one]
    rw [columnBorn, hc, pmul_single_single, Gauss.mul_one, mono_one_mul, List.append_nil]
  rw [normPair, ket0, hone, columnBorn_nil, List.append_nil]
  exact polySame_refl _

theorem scale_ket0 (P : Poly) : polySame (pmul (normPair ket0) P) P :=
  polySame.trans (polySame_pmul_left normPair_ket0 P) (fun t => by rw [one_pmul])

/-- Con `|φ⟩ = |0⟩`, `‖φ‖²` è la costante `1` e si ritrova `marginal_ui`. -/
theorem marginal_ui_from_gen (U : Mat) (ψ : Pair) :
    pairSame (marginalLeft (applyUI U (tensorPair ψ ket0))) (bornPair (applyMat U ψ)) := by
  refine pairSame.trans (marginal_left_gen U ψ ket0) ?_
  unfold pairSame scalePair bornPair
  exact ⟨scale_ket0 _, scale_ket0 _⟩

/-- Con `|ψ⟩ = |0⟩`, `‖ψ‖²` è la costante `1` e si ritrova `marginal_iu`. -/
theorem marginal_iu_from_gen (U : Mat) (φ : Pair) :
    pairSame (marginalRight (applyIU U (tensorPair ket0 φ))) (bornPair (applyMat U φ)) := by
  refine pairSame.trans (marginal_right_gen U ket0 φ) ?_
  unfold pairSame scalePair bornPair
  exact ⟨scale_ket0 _, scale_ket0 _⟩

def genericPair : Pair := ⟨genericA, genericB⟩

theorem normPair_generic :
    polySame (psub (normPair genericPair) (single 1 Mono.one)) gA := by
  simpa only [normPair, genericPair] using
    polySame.trans (polySame_psub (born_norm genericA genericB) (polySame_refl _)) generic_sphere

theorem scale_defect (μ P : Poly) (hμ : polySame (psub μ (single 1 Mono.one)) gA) :
    inIdeal3 (psub (pmul μ P) P) := by
  refine ⟨[], [], P, ?_⟩
  intro t
  have hone : polySame P (pmul (single 1 Mono.one) P) := fun t => by rw [one_pmul]
  have hstep : polySame (psub (pmul μ P) P) (pmul gA P) :=
    polySame.trans (polySame_psub (polySame_refl _) hone)
      (polySame.trans (polySame.symm (polySame_mul_psub_left μ (single 1 Mono.one) P))
        (polySame_pmul_left hμ P))
  have hcomm : polySame (pmul gA P) (pmul P gA) := polySame_mul_comm gA P
  rw [hstep t, hcomm t]
  simp [pmul, Universe.Quotient.mul, List.nil_append]

/-- Sul fattore destro generico, `marginale − Pᵢ(U|ψ⟩)` ha cofattore `gA`. -/
theorem marginal_left_sphere (U : Mat) (ψ : Pair) :
    inIdeal3 (psub (marginalLeft (applyUI U (tensorPair ψ genericPair))).a0
        (bornPair (applyMat U ψ)).a0) ∧
      inIdeal3 (psub (marginalLeft (applyUI U (tensorPair ψ genericPair))).a1
        (bornPair (applyMat U ψ)).a1) := by
  have hμ := normPair_generic
  have hgen := marginal_left_gen U ψ genericPair
  exact
    ⟨inIdeal3_polySame (polySame_psub hgen.1 (polySame_refl _))
        (scale_defect (normPair genericPair) (bornPair (applyMat U ψ)).a0 hμ),
      inIdeal3_polySame (polySame_psub hgen.2 (polySame_refl _))
        (scale_defect (normPair genericPair) (bornPair (applyMat U ψ)).a1 hμ)⟩

/-- Sul fattore sinistro generico, `marginale − Pᵢ(U|φ⟩)` ha cofattore `gA`. -/
theorem marginal_right_sphere (U : Mat) (φ : Pair) :
    inIdeal3 (psub (marginalRight (applyIU U (tensorPair genericPair φ))).a0
        (bornPair (applyMat U φ)).a0) ∧
      inIdeal3 (psub (marginalRight (applyIU U (tensorPair genericPair φ))).a1
        (bornPair (applyMat U φ)).a1) := by
  have hμ := normPair_generic
  have hgen := marginal_right_gen U genericPair φ
  exact
    ⟨inIdeal3_polySame (polySame_psub hgen.1 (polySame_refl _))
        (scale_defect (normPair genericPair) (bornPair (applyMat U φ)).a0 hμ),
      inIdeal3_polySame (polySame_psub hgen.2 (polySame_refl _))
        (scale_defect (normPair genericPair) (bornPair (applyMat U φ)).a1 hμ)⟩

end Universe.Composition
