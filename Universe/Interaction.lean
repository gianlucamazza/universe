/-
Interazione da un'Hamiltoniana.

`G = |1⟩⟨1| ⊗ (n·σ)` sulle celle `2i + k`. Non è un'involuzione:
`G² = |1⟩⟨1| ⊗ I` modulo `gN` e `G³ = G`. Se `a³ = a`, i coefficienti di
`exp(−i φ a)` sono quelli di `(1 − a²) + cos φ · a² − i sin φ · a`
(`Universe.Series.expCoeff_idem`). Su `G` quella forma è
`|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`.

Nel punto `c = 0`, `s = 1`, `n = e_x` si ha `U = −i X`: l'evoluzione
controllata è `CNOT` seguito dalla fase `−i` sul `|1⟩` del controllo.
Su `|ψ⟩ ⊗ |0⟩` lo stato è `α|00⟩ − i β|11⟩`. La fase ha modulo uno, quindi
esce da ogni peso di Born: `decoherence` e `pointer_born` restano gli stessi.

Con l'apparato in `|0⟩` lo stato è `α|00⟩ + β|1⟩⊗(U|0⟩)`.
`partial_coherence` dice che l'antidiagonale del sistema ridotto è
`α β̄ · conj(⟨0|U|0⟩)`, con `⟨0|U|0⟩ = c − i s nz`, nell'anello libero.
`partial_diagonal` mette la diagonale su `bornPair`, modulo `(gC, gN)`:
è la norma di colonna di `U`. `ψ` valutato in `3/5`, `−4/5 i` e il
coupling lungo `e_x` danno i tre punti `(1, 0)`, `(3/5, 4/5)` e `(0, 1)`.

La lettura del puntatore è `condition`: lo stato del sistema, non
normalizzato, quando l'apparato è su `|k⟩`. Dopo `CNOT` su `|ψ⟩ ⊗ |0⟩`,
`luders` dà `(α, 0)` e `(0, β)`, con norme `bornPair`. `repeatable`
applica un secondo `CNOT` a un apparato fresco: l'esito `k` pesa quanto
la norma e l'altro esito pesa zero. Nel punto `c = 3/5`, `s = 4/5`,
`n = e_x` le norme sono `9/25` e `16/25`.
-/
import Universe.Observer
import Universe.Series

namespace Universe.Interaction

open Universe.Ring
open Universe.Series
open Universe.Quotient hiding mul
open Universe.Dynamics
open Universe.Qubit
open Universe.Epistemology
open Universe.Evaluation
open Universe.Composition
open Universe.Observer

/-! ### Operatori a blocchi: idle sul controllo `|0⟩`, matrice sul `|1⟩` -/

@[ext]
structure Gate where
  idle : Poly
  hot : Mat

def gateMul (G H : Gate) : Gate := ⟨pmul G.idle H.idle, matMul G.hot H.hot⟩

def gateAdd (G H : Gate) : Gate := ⟨G.idle ++ H.idle, matAdd G.hot H.hot⟩

def gateSmul (z : Gauss) (G : Gate) : Gate := ⟨scale z G.idle, matSmul z G.hot⟩

def gateScale (p : Poly) (G : Gate) : Gate := ⟨pmul p G.idle, matScale p G.hot⟩

def gateNeg (G : Gate) : Gate := ⟨pneg G.idle, matNeg G.hot⟩

def gateOne : Gate := ⟨single 1 Mono.one, matOne⟩

def gateZero : Gate := ⟨[], matZero⟩

/-- `G = |1⟩⟨1| ⊗ H`. Il blocco `|0⟩` è zero. -/
def generator : Gate := ⟨[], hamiltonian⟩

def gateRel (G H : Gate) : Prop := polySame G.idle H.idle ∧ matRel G.hot H.hot

theorem gateRel_refl (G : Gate) : gateRel G G := ⟨polySame_refl _, matRel_refl _⟩

theorem gateRel_symm {G H : Gate} (h : gateRel G H) : gateRel H G :=
  ⟨h.1.symm, matRel_symm h.2⟩

theorem gateRel_trans {G H K : Gate} (hGH : gateRel G H) (hHK : gateRel H K) :
    gateRel G K :=
  ⟨hGH.1.trans hHK.1, matRel_trans hGH.2 hHK.2⟩

instance gateSetoid : Setoid Gate where
  r := gateRel
  iseqv := ⟨gateRel_refl, fun h => gateRel_symm h, fun h1 h2 => gateRel_trans h1 h2⟩

abbrev QGate := Quotient gateSetoid

theorem gateMul_right_rel (G : Gate) {H H' : Gate} (h : gateRel H H') :
    gateRel (gateMul G H) (gateMul G H') :=
  ⟨polySame_pmul_right h.1 G.idle, matMul_right_rel G.hot h.2⟩

theorem gateMul_left_rel {G G' : Gate} (h : gateRel G G') (H : Gate) :
    gateRel (gateMul G H) (gateMul G' H) :=
  ⟨polySame_pmul_left h.1 H.idle, matMul_left_rel h.2 H.hot⟩

theorem gateAdd_rel {G G' H H' : Gate} (hG : gateRel G G') (hH : gateRel H H') :
    gateRel (gateAdd G H) (gateAdd G' H') :=
  ⟨polySame_append hG.1 hH.1, matAdd_rel hG.2 hH.2⟩

theorem gateSmul_rel (z : Gauss) {G H : Gate} (h : gateRel G H) :
    gateRel (gateSmul z G) (gateSmul z H) :=
  ⟨polySame_scale z h.1, matSmul_rel z h.2⟩

noncomputable def qgmul (x y : QGate) : QGate :=
  Quot.lift
    (fun G : Gate =>
      Quot.lift (fun H : Gate => Quotient.mk gateSetoid (gateMul G H))
        (fun _ _ h => Quotient.sound (gateMul_right_rel G h)) y)
    (fun G G' h => by
      induction y using Quotient.ind with
      | _ H =>
        apply Quotient.sound
        exact gateMul_left_rel h H)
    x

noncomputable def qgadd (x y : QGate) : QGate :=
  Quotient.lift₂ (fun G H => Quotient.mk gateSetoid (gateAdd G H))
    (fun _ _ _ _ hG hH => Quotient.sound (gateAdd_rel hG hH)) x y

noncomputable def qgsmul (z : Gauss) (x : QGate) : QGate :=
  Quotient.lift (fun G => Quotient.mk gateSetoid (gateSmul z G))
    (fun _ _ h => Quotient.sound (gateSmul_rel z h)) x

theorem qgmul_mk (G H : Gate) :
    qgmul (Quotient.mk gateSetoid G) (Quotient.mk gateSetoid H) =
      Quotient.mk gateSetoid (gateMul G H) :=
  rfl

theorem qgadd_mk (G H : Gate) :
    qgadd (Quotient.mk gateSetoid G) (Quotient.mk gateSetoid H) =
      Quotient.mk gateSetoid (gateAdd G H) :=
  rfl

theorem qgsmul_mk (z : Gauss) (G : Gate) :
    qgsmul z (Quotient.mk gateSetoid G) = Quotient.mk gateSetoid (gateSmul z G) :=
  rfl

theorem gateMul_one_left (G : Gate) : gateMul gateOne G = G := by
  apply Gate.ext
  · exact one_pmul G.idle
  · exact matMul_one_left G.hot

theorem gateMul_one_right (G : Gate) : gateMul G gateOne = G := by
  apply Gate.ext
  · exact pmul_one G.idle
  · exact matMul_one_right G.hot

theorem gateAdd_zero (G : Gate) : gateAdd G gateZero = G := by
  apply Gate.ext
  · exact List.append_nil G.idle
  · exact matAdd_zero G.hot

theorem gateZero_add (G : Gate) : gateAdd gateZero G = G := by
  apply Gate.ext
  · rfl
  · exact matZero_add G.hot

theorem gateSmul_one (G : Gate) : gateSmul 1 G = G := by
  apply Gate.ext
  · exact scale_one G.idle
  · exact matSmul_one G.hot

theorem gateSmul_mul (z w : Gauss) (G : Gate) :
    gateSmul (z * w) G = gateSmul z (gateSmul w G) := by
  apply Gate.ext
  · exact scale_mul_gauss z w G.idle
  · exact matSmul_mul_gauss z w G.hot

theorem gateSmul_add (z : Gauss) (G H : Gate) :
    gateSmul z (gateAdd G H) = gateAdd (gateSmul z G) (gateSmul z H) := by
  apply Gate.ext
  · exact scale_append z G.idle H.idle
  · exact matSmul_add z G.hot H.hot

theorem gateMul_assoc_rel (G H K : Gate) :
    gateRel (gateMul (gateMul G H) K) (gateMul G (gateMul H K)) :=
  ⟨polySame_pmul_assoc _ _ _, matRel_of_matSame (matMul_assoc _ _ _)⟩

noncomputable def gateDyn : Dyn QGate where
  mul := qgmul
  add := qgadd
  one := Quotient.mk gateSetoid gateOne
  zero := Quotient.mk gateSetoid gateZero
  smul := qgsmul
  mul_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro G H K
    rw [qgmul_mk, qgmul_mk, qgmul_mk, qgmul_mk]
    exact Quotient.sound (gateMul_assoc_rel G H K)
  one_mul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro G
    rw [qgmul_mk, gateMul_one_left]
  mul_one := by
    intro x
    refine Quotient.inductionOn x ?_
    intro G
    rw [qgmul_mk, gateMul_one_right]
  add_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro G
    rw [qgadd_mk, gateAdd_zero]
  zero_add := by
    intro x
    refine Quotient.inductionOn x ?_
    intro G
    rw [qgadd_mk, gateZero_add]
  smul_one := by
    intro x
    refine Quotient.inductionOn x ?_
    intro G
    rw [qgsmul_mk, gateSmul_one]
  zero_smul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro G
    rw [qgsmul_mk]
    exact Quotient.sound ⟨polySame_scale_zero G.idle, matZero_smul_rel G.hot⟩
  smul_mul := by
    intro z w x
    refine Quotient.inductionOn x ?_
    intro G
    rw [qgsmul_mk, qgsmul_mk, qgsmul_mk, gateSmul_mul]
  smul_add := by
    intro z x y
    refine Quotient.inductionOn₂ x y ?_
    intro G H
    rw [qgadd_mk, qgsmul_mk, qgsmul_mk, qgsmul_mk, qgadd_mk, gateSmul_add]

def GQ : QGate := Quotient.mk gateSetoid generator

/-- `G² = |1⟩⟨1| ⊗ I` modulo `gN`. Il blocco `|0⟩` è zero dai due lati. -/
theorem generator_sq : gateRel (gateMul generator generator) ⟨[], matOne⟩ :=
  ⟨polySame_refl _, hamiltonian_sq⟩

theorem generator_square : gateDyn.mul GQ GQ = Quotient.mk gateSetoid ⟨[], matOne⟩ := by
  have hmul : gateDyn.mul = qgmul := by unfold gateDyn; rfl
  rw [hmul, GQ, qgmul_mk]
  exact Quotient.sound generator_sq

theorem generator_mul_projector : gateMul ⟨[], matOne⟩ generator = generator := by
  apply Gate.ext
  · rfl
  · exact matMul_one_left hamiltonian

/-- `G³ = G`, per moltiplicazione da `G² = |1⟩⟨1| ⊗ I`. -/
theorem generator_cube : gateDyn.mul (gateDyn.mul GQ GQ) GQ = GQ := by
  rw [generator_square]
  have hmul : gateDyn.mul = qgmul := by unfold gateDyn; rfl
  rw [hmul, GQ, qgmul_mk, generator_mul_projector]

/-- Istanza di `expCoeff_idem` su `G`. -/
theorem expCoeff_generator (n : Nat) :
    expSeries gateDyn GQ n = closedIdem gateDyn GQ n :=
  expCoeff_idem gateDyn GQ generator_cube n

/-- `(1 − G²) + c G² − i s G`. A grado zero `(1 − G²) + G²` vale `1`. -/
def closedGenerator : Gate :=
  gateAdd
    (gateAdd
      (gateAdd gateOne (gateNeg (gateMul generator generator)))
      (gateScale cP (gateMul generator generator)))
    (gateScale gamma generator)

/-- `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`. -/
def controlledEvolution : Gate := ⟨single 1 Mono.one, evolution⟩

theorem polySame_unit_cancel :
    polySame (single (1 : Gauss) Mono.one ++ pneg (single (1 : Gauss) Mono.one)) [] := by
  intro t
  rw [show pneg (single (1 : Gauss) Mono.one) = single (-1) Mono.one from rfl]
  rw [coeffOf_append, coeff_single_eq, coeff_single_eq, coeffOf_nil]
  by_cases ht : Mono.one = t
  · rw [ite_eq_left ht, ite_eq_left ht]
    exact Gauss.add_neg_cancel (1 : Gauss)
  · rw [ite_eq_right ht, ite_eq_right ht, Gauss.zero_add]

theorem matOne_sub_one : matSame (matAdd matOne (matNeg matOne)) matZero := by
  refine ⟨?_, polySame_refl _, polySame_refl _, ?_⟩
  · simpa only [matAdd, matNeg, matOne, matZero] using polySame_unit_cancel
  · simpa only [matAdd, matNeg, matOne, matZero] using polySame_unit_cancel

theorem closedGenerator_idle : polySame closedGenerator.idle (single (1 : Gauss) Mono.one) := by
  have hmul : (gateMul generator generator).idle = [] := rfl
  rw [show closedGenerator.idle =
      (((gateOne.idle ++ (gateNeg (gateMul generator generator)).idle) ++
          (gateScale cP (gateMul generator generator)).idle) ++
        (gateScale gamma generator).idle) from rfl]
  rw [show gateOne.idle = single (1 : Gauss) Mono.one from rfl]
  rw [show (gateNeg (gateMul generator generator)).idle =
      pneg (gateMul generator generator).idle from rfl, hmul]
  rw [show pneg ([] : Poly) = [] from rfl]
  rw [show (gateScale cP (gateMul generator generator)).idle =
      pmul cP (gateMul generator generator).idle from rfl, hmul, pmul_nil]
  rw [show (gateScale gamma generator).idle = pmul gamma generator.idle from rfl]
  rw [show generator.idle = [] from rfl, pmul_nil]
  exact polySame.trans (polySame_append_nil _)
    (polySame.trans (polySame_append_nil _) (polySame_append_nil _))

theorem hot_matches_evolution :
    matAdd (matScale cP matOne) (matScale gamma hamiltonian) = evolution := by
  apply Mat.ext
  · rfl
  · rw [show (matAdd (matScale cP matOne) (matScale gamma hamiltonian)).a01 =
        pmul cP [] ++ pmul gamma hamiltonian.a01 from rfl, pmul_nil]
    rfl
  · rw [show (matAdd (matScale cP matOne) (matScale gamma hamiltonian)).a10 =
        pmul cP [] ++ pmul gamma hamiltonian.a10 from rfl, pmul_nil]
    rfl
  · rfl

theorem closedGenerator_hot :
    closedGenerator.hot =
      matAdd
        (matAdd (matAdd matOne (matNeg (matMul hamiltonian hamiltonian)))
          (matScale cP (matMul hamiltonian hamiltonian)))
        (matScale gamma hamiltonian) :=
  rfl

/-- `exp(−i φ G)` ha i coefficienti di `closedIdem` (`expCoeff_generator`).
Quella forma, letta con `c` e `s`, è l'evoluzione controllata. -/
theorem controlled_from_hamiltonian : gateRel closedGenerator controlledEvolution := by
  refine ⟨closedGenerator_idle, ?_⟩
  rw [closedGenerator_hot]
  let H2 := matMul hamiltonian hamiltonian
  have hH2 : matRel H2 matOne := hamiltonian_sq
  have hNeg : matRel (matNeg H2) (matNeg matOne) := matNeg_rel hH2
  have hSub : matRel (matAdd matOne (matNeg H2)) (matAdd matOne (matNeg matOne)) :=
    matAdd_rel (matRel_refl _) hNeg
  have hSub0 : matRel (matAdd matOne (matNeg matOne)) matZero :=
    matRel_of_matSame matOne_sub_one
  have hScale : matRel (matScale cP H2) (matScale cP matOne) := matScale_rel cP hH2
  have hLeft : matRel (matAdd (matAdd matOne (matNeg H2)) (matScale cP H2))
      (matAdd matZero (matScale cP matOne)) :=
    matRel_trans (matAdd_rel hSub hScale) (matAdd_rel hSub0 (matRel_refl _))
  have hZero : matAdd matZero (matScale cP matOne) = matScale cP matOne := matZero_add _
  have hHot : matRel
      (matAdd (matAdd (matAdd matOne (matNeg H2)) (matScale cP H2))
        (matScale gamma hamiltonian))
      (matAdd (matScale cP matOne) (matScale gamma hamiltonian)) :=
    matRel_trans (matAdd_rel hLeft (matRel_refl _)) (by rw [hZero]; exact matRel_refl _)
  exact matRel_trans hHot (by rw [hot_matches_evolution]; exact matRel_refl _)

/-! ### Azione sullo stato e punto `CNOT` -/

/-- `G` agisce come `H` sul blocco del controllo `|1⟩` e come zero sull'altro. -/
def applyGen (H : Mat) (v : Quad) : Quad where
  a0 := []
  a1 := []
  a2 := pmul H.a00 v.a2 ++ pmul H.a01 v.a3
  a3 := pmul H.a10 v.a2 ++ pmul H.a11 v.a3

/-- `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`. -/
def applyCtrl (U : Mat) (v : Quad) : Quad where
  a0 := v.a0
  a1 := v.a1
  a2 := pmul U.a00 v.a2 ++ pmul U.a01 v.a3
  a3 := pmul U.a10 v.a2 ++ pmul U.a11 v.a3

def applyGate (G : Gate) (v : Quad) : Quad where
  a0 := pmul G.idle v.a0
  a1 := pmul G.idle v.a1
  a2 := pmul G.hot.a00 v.a2 ++ pmul G.hot.a01 v.a3
  a3 := pmul G.hot.a10 v.a2 ++ pmul G.hot.a11 v.a3

/-- Fase sul `|1⟩` del controllo: scala le celle `|10⟩` e `|11⟩`. -/
def phaseControl (z : Gauss) (v : Quad) : Quad where
  a0 := v.a0
  a1 := v.a1
  a2 := scale z v.a2
  a3 := scale z v.a3

theorem applyGate_generator (v : Quad) : applyGate generator v = applyGen hamiltonian v := by
  simp [applyGate, applyGen, generator, pmul_nil_left]

theorem applyGate_controlled (v : Quad) :
    applyGate controlledEvolution v = applyCtrl evolution v := by
  simp [applyGate, applyCtrl, controlledEvolution, one_pmul]

/-- `c = 0`, `s = 1`, `n = e_x`. Si tengono `s` e `nx`, azzerandone l'esponente. -/
def keepFlip (m : Mono) : Option Mono :=
  if m.c = 0 ∧ m.ny = 0 ∧ m.nz = 0 then some {m with s := 0, nx := 0} else none

theorem keepFlip_mul (m n : Mono) : keepFlip (m.mul n) = optionMul (keepFlip m) (keepFlip n) := by
  unfold keepFlip optionMul
  by_cases hmc : m.c = 0 <;> by_cases hmy : m.ny = 0 <;> by_cases hmz : m.nz = 0 <;>
      by_cases hnc : n.c = 0 <;> by_cases hny : n.ny = 0 <;> by_cases hnz : n.nz = 0 <;>
      simp [Mono.mul, hmc, hmy, hmz, hnc, hny, hnz, Nat.add_eq_zero_iff] <;>
      (try (congr 1; ext <;> rfl))

def specQuad (keep : Mono → Option Mono) (v : Quad) : Quad where
  a0 := specPoly keep v.a0
  a1 := specPoly keep v.a1
  a2 := specPoly keep v.a2
  a3 := specPoly keep v.a3

theorem keepFlip_c1 : keepFlip c1 = none := by
  simp [keepFlip, c1]

theorem keepFlip_s_nx : keepFlip (s1.mul nx1) = some Mono.one := by
  simp [keepFlip, Mono.mul, s1, nx1, Mono.one]

theorem keepFlip_s_ny : keepFlip (s1.mul ny1) = none := by
  simp [keepFlip, Mono.mul, s1, ny1]

theorem keepFlip_s_nz : keepFlip (s1.mul nz1) = none := by
  simp [keepFlip, Mono.mul, s1, nz1]

theorem mulMono_single (a b : Gauss) (m n : Mono) :
    mulMono a m (single b n) = single (a * b) (m.mul n) :=
  rfl

theorem specFlip_single_none (a : Gauss) (m : Mono) (hm : keepFlip m = none) :
    specPoly keepFlip (single a m) = [] := by
  simp [specPoly, single, hm]

theorem specFlip_single_some (a : Gauss) (m k : Mono) (hm : keepFlip m = some k) :
    specPoly keepFlip (single a m) = single a k := by
  simp [specPoly, single, hm]

theorem specFlip_a00 : specPoly keepFlip evolution.a00 = [] := by
  rw [show evolution.a00 = pmul cP (single 1 Mono.one) ++ pmul gamma h00 from rfl]
  rw [pmul_one, gamma, h00, pmul_single_list, mulMono_single, List.append_nil, cP]
  rw [spec_append, specFlip_single_none _ _ keepFlip_c1, specFlip_single_none _ _ keepFlip_s_nz]
  rfl

theorem specFlip_a11 : specPoly keepFlip evolution.a11 = [] := by
  rw [show evolution.a11 = pmul cP (single 1 Mono.one) ++ pmul gamma h11 from rfl]
  rw [pmul_one, gamma, h11, pmul_single_list, mulMono_single, List.append_nil, cP]
  rw [spec_append, specFlip_single_none _ _ keepFlip_c1, specFlip_single_none _ _ keepFlip_s_nz]
  rfl

theorem specFlip_a01 : specPoly keepFlip evolution.a01 = single (-Gauss.i) Mono.one := by
  rw [show evolution.a01 = pmul gamma h01 from rfl, gamma, h01, pmul_single_list, mulMono_append,
    mulMono_single, mulMono_single, List.append_nil]
  rw [spec_append, specFlip_single_some _ _ _ keepFlip_s_nx, specFlip_single_none _ _ keepFlip_s_ny,
    Gauss.mul_one, List.append_nil]

theorem specFlip_a10 : specPoly keepFlip evolution.a10 = single (-Gauss.i) Mono.one := by
  rw [show evolution.a10 = pmul gamma h10 from rfl, gamma, h10, pmul_single_list, mulMono_append,
    mulMono_single, mulMono_single, List.append_nil]
  rw [spec_append, specFlip_single_some _ _ _ keepFlip_s_nx, specFlip_single_none _ _ keepFlip_s_ny,
    Gauss.mul_one, List.append_nil]

/-- `CNOT` e poi la fase `−i` sul controllo: `α|00⟩ − i β|11⟩`. -/
theorem phase_cnot (ψ : Pair) :
    phaseControl (-Gauss.i) (applyCNOT (tensorPair ψ ket0)) =
      ⟨ψ.a0, [], [], scale (-Gauss.i) ψ.a1⟩ := by
  rw [cnot_ket0]
  rfl

/-- Nel punto `c = 0`, `s = 1`, `n = e_x` l'evoluzione controllata è `CNOT`
seguito dalla fase `−i` sul `|1⟩` del controllo. Su `|ψ⟩ ⊗ |0⟩` i due stati,
dopo `keepFlip`, hanno gli stessi coefficienti. -/
theorem cnot_point (ψ : Pair) :
    quadSame (specQuad keepFlip (applyCtrl evolution (tensorPair ψ ket0)))
      (specQuad keepFlip (phaseControl (-Gauss.i) (applyCNOT (tensorPair ψ ket0)))) := by
  rw [cnot_ket0, tensor_idle_right]
  simp only [applyCtrl, phaseControl, specQuad, quadSame, pmul_nil]
  refine And.intro (polySame_refl _) (And.intro (polySame_refl _) (And.intro ?_ ?_))
  · rw [spec_append]
    refine polySame.trans
      (polySame_append (spec_pmul keepFlip_mul evolution.a00 ψ.a1) (polySame_refl _)) ?_
    rw [specFlip_a00]
    simp only [specPoly, pmul_nil_left]
    exact polySame_refl _
  · rw [spec_append, spec_scale]
    refine polySame.trans
      (polySame_append (spec_pmul keepFlip_mul evolution.a10 ψ.a1) (polySame_refl _)) ?_
    rw [specFlip_a10, pmul_unit_scale]
    simp only [specPoly]
    exact polySame_append_nil _

/-- `CNOT` seguito dalla fase `−i`, su `|ψ⟩ ⊗ |0⟩`. -/
def phasedPoint (ψ : Pair) : Quad :=
  phaseControl (-Gauss.i) (applyCNOT (tensorPair ψ ket0))

/-- La fase `−i` ha modulo uno, quindi esce da ogni peso di Born.

`decoherence` e `pointer_born` restano gli stessi: l'antidiagonale dello stato
ridotto è il polinomio zero e la diagonale è `bornPair`, nell'anello libero,
sia per il sistema sia per l'apparato. -/
theorem cnot_point_born (ψ : Pair) :
    (polySame (reduceLeft (phasedPoint ψ)).a01 [] ∧
        polySame (reduceLeft (phasedPoint ψ)).a10 [] ∧
          pairSame ⟨(reduceLeft (phasedPoint ψ)).a00, (reduceLeft (phasedPoint ψ)).a11⟩
            (bornPair ψ)) ∧
      (polySame (reduceRight (phasedPoint ψ)).a01 [] ∧
        polySame (reduceRight (phasedPoint ψ)).a10 [] ∧
          pairSame ⟨(reduceRight (phasedPoint ψ)).a00, (reduceRight (phasedPoint ψ)).a11⟩
            (bornPair ψ)) := by
  unfold phasedPoint
  rw [phase_cnot]
  have hz : (-Gauss.i) * Gauss.conj (-Gauss.i) = 1 := by rw [conj_neg_i, minus_i_mul_i]
  have hborn : columnBorn (scale (-Gauss.i) ψ.a1) = columnBorn ψ.a1 :=
    columnBorn_unit_phase _ _ hz
  refine ⟨?_, ?_⟩
  · simp only [reduceLeft, bornPair, pairSame, columnBorn_nil, conjP, pmul_nil, pmul_nil_left,
      List.append_nil, List.nil_append, hborn]
    exact ⟨polySame_refl _, polySame_refl _, polySame_refl _, polySame_refl _⟩
  · simp only [reduceRight, bornPair, pairSame, columnBorn_nil, conjP, pmul_nil, pmul_nil_left,
      List.append_nil, List.nil_append, hborn]
    exact ⟨polySame_refl _, polySame_refl _, polySame_refl _, polySame_refl _⟩

/-! ### Misura parziale -/

/-- Evoluzione controllata su `|ψ⟩ ⊗ |0⟩`: `α|00⟩ + β|1⟩⊗(U|0⟩)`. -/
def partialState (ψ : Pair) : Quad :=
  applyCtrl evolution (tensorPair ψ ket0)

/-- Le quattro celle: `α`, `0`, `β ⟨0|U|0⟩`, `β ⟨1|U|0⟩`. -/
theorem partial_state_cells (ψ : Pair) :
    partialState ψ =
      ⟨ψ.a0, [], pmul evolution.a00 ψ.a1, pmul evolution.a10 ψ.a1⟩ := by
  rw [partialState, tensor_idle_right]
  simp only [applyCtrl, pmul_nil, List.append_nil]

/-- L'antidiagonale del sistema ridotto è `α β̄ · conj(⟨0|U|0⟩)`.

`⟨0|U|0⟩ = c − i s nz`. L'identità sta nell'anello libero. L'altra
entrata è `β ᾱ · ⟨0|U|0⟩`. -/
theorem partial_coherence (ψ : Pair) :
    polySame (reduceLeft (partialState ψ)).a01
      (pmul (pmul ψ.a0 (conjP ψ.a1)) (conjP evolution.a00)) ∧
    polySame (reduceLeft (partialState ψ)).a10
      (pmul (pmul ψ.a1 (conjP ψ.a0)) evolution.a00) ∧
    evolution.a00 = single (1 : Gauss) c1 ++ single (-Gauss.i) (s1.mul nz1) := by
  refine ⟨?_, ?_, evolution_a00_bin⟩
  · rw [partial_state_cells]
    simp only [reduceLeft, pmul_nil_left, List.append_nil]
    rw [conj_pmul]
    exact polySame.trans (slide_right ψ.a0 (conjP evolution.a00) (conjP ψ.a1))
      (polySame_mul_comm (conjP evolution.a00) (pmul ψ.a0 (conjP ψ.a1)))
  · rw [partial_state_cells]
    simp only [reduceLeft]
    rw [show conjP ([] : Poly) = [] from rfl, pmul_nil, List.append_nil]
    exact polySame.trans
      (polySame_mul_comm (pmul evolution.a00 ψ.a1) (conjP ψ.a0))
      (polySame.trans (slide_right (conjP ψ.a0) evolution.a00 ψ.a1)
        (polySame.trans (polySame_mul_comm evolution.a00 (pmul (conjP ψ.a0) ψ.a1))
          (polySame_pmul_left (polySame_mul_comm (conjP ψ.a0) ψ.a1) evolution.a00)))

/-- La diagonale è `bornPair`, modulo `(gC, gN)`.

`|α|²` sta nell'anello libero. `|β|²` usa la norma della prima colonna
di `U`: `(U†U)₀₀ − 1` è `δ`. -/
theorem partial_diagonal (ψ : Pair) :
    inIdeal (psub (reduceLeft (partialState ψ)).a00 (columnBorn ψ.a0)) ∧
      inIdeal (psub (reduceLeft (partialState ψ)).a11 (columnBorn ψ.a1)) := by
  refine ⟨?_, ?_⟩
  · have h00 : polySame (reduceLeft (partialState ψ)).a00 (columnBorn ψ.a0) := by
      rw [partial_state_cells]
      simp only [reduceLeft, columnBorn_nil, List.append_nil]
      exact polySame_refl _
    exact inIdeal_of_polySame h00
  · have hcells : polySame (reduceLeft (partialState ψ)).a11
        (pmul (columnBorn ψ.a1) ((matMul (matDagger evolution) evolution).a00)) := by
      rw [partial_state_cells]
      simp only [reduceLeft]
      exact polySame.trans (marginal_scale_col ψ.a1 evolution.a00 evolution.a10)
        (polySame_pmul_right ground_born_sum (columnBorn ψ.a1))
    have hdist : polySame
        (psub (pmul (columnBorn ψ.a1) ((matMul (matDagger evolution) evolution).a00))
          (columnBorn ψ.a1))
        (pmul (columnBorn ψ.a1) unitaryDefect) := by
      have hone : pmul (columnBorn ψ.a1) (single (1 : Gauss) Mono.one) = columnBorn ψ.a1 :=
        pmul_one _
      have hsub : polySame
          (psub (pmul (columnBorn ψ.a1) ((matMul (matDagger evolution) evolution).a00))
            (pmul (columnBorn ψ.a1) (single (1 : Gauss) Mono.one)))
          (pmul (columnBorn ψ.a1)
            (psub ((matMul (matDagger evolution) evolution).a00) (single (1 : Gauss) Mono.one))) :=
        polySame.symm (polySame_mul_psub_right (columnBorn ψ.a1) _ _)
      have hdefect : polySame
          (pmul (columnBorn ψ.a1)
            (psub ((matMul (matDagger evolution) evolution).a00) (single (1 : Gauss) Mono.one)))
          (pmul (columnBorn ψ.a1) unitaryDefect) :=
        polySame_pmul_right evolution_unitary_00 _
      have hborn : polySame (columnBorn ψ.a1)
          (pmul (columnBorn ψ.a1) (single (1 : Gauss) Mono.one)) :=
        fun _ => by rw [hone]
      exact polySame.trans (polySame_psub (polySame_refl _) hborn) (polySame.trans hsub hdefect)
    exact inIdeal_polySame
      (polySame.trans (polySame_psub hcells (polySame_refl _)) hdist)
      (inIdeal_mul_left (columnBorn ψ.a1) unitary_ideal)

/-! ### Punti: `ψ` già valutato, coupling lungo `e_x` -/

/-- `Φ|0⟩` nel punto `c = 3/5`, `s = 4/5`: `α = 3/5`, `β = −4/5 i`.

Il coupling tiene i propri `c, s`. Un solo monomio non porta entrambi. -/
def probePair : Pair := ⟨single pointAlpha Mono.one, single pointBeta Mono.one⟩

theorem probe_coherence_factor :
    pointAlpha * Gauss.conj pointBeta = ⟨0, (12 : Rat) / 25⟩ := by
  simp only [pointAlpha, pointBeta, pointC, pointS, Gauss.conj]
  ext <;> simp <;> grind

/-- Sul probe, l'antidiagonale è `(12/25 i) · conj(⟨0|U|0⟩)`. -/
theorem probe_coh01 :
    polySame (reduceLeft (partialState probePair)).a01
      (scale ⟨0, (12 : Rat) / 25⟩ (conjP evolution.a00)) := by
  have h := (partial_coherence probePair).1
  unfold probePair at h
  have hinner : pmul (single pointAlpha Mono.one) (conjP (single pointBeta Mono.one)) =
      single ⟨0, (12 : Rat) / 25⟩ Mono.one := by
    rw [show conjP (single pointBeta Mono.one) = single (Gauss.conj pointBeta) Mono.one from rfl]
    rw [pmul_single_single, mono_one_mul, List.append_nil, probe_coherence_factor]
  rw [hinner, pmul_unit_scale] at h
  exact h

/-- L'altra entrata è `−(12/25 i) · ⟨0|U|0⟩`. -/
theorem probe_coh10 :
    polySame (reduceLeft (partialState probePair)).a10
      (scale ⟨0, -((12 : Rat) / 25)⟩ evolution.a00) := by
  have h := (partial_coherence probePair).2.1
  unfold probePair at h
  have hconj : Gauss.conj pointAlpha = pointAlpha := by
    simp [pointAlpha, Gauss.conj]
  have hinner : pmul (single pointBeta Mono.one) (conjP (single pointAlpha Mono.one)) =
      single ⟨0, -((12 : Rat) / 25)⟩ Mono.one := by
    rw [show conjP (single pointAlpha Mono.one) = single (Gauss.conj pointAlpha) Mono.one from rfl,
      hconj, pmul_single_single, mono_one_mul, List.append_nil, Gauss.mul_comm, point_amp_mul]
  rw [hinner, pmul_unit_scale] at h
  exact h

/-- Sul cerchio e lungo `e_x`, un polinomio dell'ideale ha lo stesso valore del suo resto. -/
theorem eval_matches_born (c s : Rat) (hc : c * c + s * s = 1) (p q : Poly)
    (h : inIdeal (psub p q)) :
    evalAt c s 1 0 0 p = evalAt c s 1 0 0 q := by
  have hzero := eval_inIdeal h c s 1 0 0 (eval_gC_on_circle c s hc) (eval_gN_axis_x c s)
  rw [eval_psub] at hzero
  exact gauss_of_sub _ _ hzero

/-- Coerenza e purezza del probe, coupling `(c, s)` sul cerchio, `n = e_x`.

La coerenza è `(12/25 i) · c`. La purezza è `337/625 + (288/625) c²`. -/
theorem partial_reading (c s : Rat) (hc : c * c + s * s = 1) :
    evalAt c s 1 0 0 (reduceLeft (partialState probePair)).a01 =
      ⟨0, ((12 : Rat) / 25) * c⟩ ∧
    evalAt c s 1 0 0 (purity (reduceLeft (partialState probePair))) =
      ⟨(337 : Rat) / 625 + ((288 : Rat) / 625) * (c * c), 0⟩ := by
  let ρ := reduceLeft (partialState probePair)
  have he00 : evalAt c s 1 0 0 ρ.a00 = ⟨(9 : Rat) / 25, 0⟩ := by
    have hsame := eval_matches_born c s hc _ _ (partial_diagonal probePair).1
    rw [hsame, probePair, eval_column_const]
    simp [pointAlpha, pointC, Gauss.conj]
    ext <;> simp <;> grind
  have he11 : evalAt c s 1 0 0 ρ.a11 = ⟨(16 : Rat) / 25, 0⟩ := by
    have hsame := eval_matches_born c s hc _ _ (partial_diagonal probePair).2
    rw [hsame, probePair, eval_column_const]
    simp [pointBeta, pointS, Gauss.conj]
    ext <;> simp <;> grind
  have he01 : evalAt c s 1 0 0 ρ.a01 = ⟨0, ((12 : Rat) / 25) * c⟩ := by
    rw [eval_polySame probe_coh01, eval_scale, eval_conj, eval_bracket_axis_x]
    simp [Gauss.conj]
    ext <;> simp <;> grind
  have he10 : evalAt c s 1 0 0 ρ.a10 = ⟨0, -(((12 : Rat) / 25) * c)⟩ := by
    rw [eval_polySame probe_coh10, eval_scale, eval_bracket_axis_x]
    ext <;> simp <;> grind
  refine ⟨he01, ?_⟩
  rw [eval_purity, he00, he01, he10, he11]
  ext <;> simp <;> grind

/-- Coupling `(1, 0)`: coerenza `12/25 i`, purezza `1`. -/
theorem point_partial_idle :
    evalAt 1 0 1 0 0 (reduceLeft (partialState probePair)).a01 = ⟨0, (12 : Rat) / 25⟩ ∧
      evalAt 1 0 1 0 0 (purity (reduceLeft (partialState probePair))) = ⟨1, 0⟩ := by
  have h := partial_reading 1 0 (by grind)
  refine ⟨?_, ?_⟩
  · rw [h.1]
    ext <;> simp <;> grind
  · rw [h.2]
    ext <;> simp <;> grind

/-- Coupling `(3/5, 4/5)`: coerenza `36/125 i`, purezza `11017/15625`. -/
theorem point_partial_mid :
    evalAt pointC pointS 1 0 0 (reduceLeft (partialState probePair)).a01 =
      ⟨0, (36 : Rat) / 125⟩ ∧
      evalAt pointC pointS 1 0 0 (purity (reduceLeft (partialState probePair))) =
        ⟨(11017 : Rat) / 15625, 0⟩ := by
  have hc : pointC * pointC + pointS * pointS = 1 := by
    simp [pointC, pointS]
    grind
  have h := partial_reading pointC pointS hc
  refine ⟨?_, ?_⟩
  · rw [h.1]
    ext <;> simp [pointC] <;> grind
  · rw [h.2]
    ext <;> simp [pointC] <;> grind

/-- Coupling `(0, 1)`: coerenza `0`, purezza `337/625`. -/
theorem point_partial_flip :
    evalAt 0 1 1 0 0 (reduceLeft (partialState probePair)).a01 = 0 ∧
      evalAt 0 1 1 0 0 (purity (reduceLeft (partialState probePair))) =
        ⟨(337 : Rat) / 625, 0⟩ := by
  have h := partial_reading 0 1 (by grind)
  refine ⟨?_, ?_⟩
  · rw [h.1]
    ext <;> simp <;> grind
  · rw [h.2]
    ext <;> simp <;> grind

/-! ### Lettura del puntatore -/

/-- Secondo `CNOT`, apparato fresco in `|0⟩`, sullo stato già condizionato. -/
def reread (k : Fin 2) (ψ : Pair) : Quad :=
  applyCNOT (tensorPair (condition k (applyCNOT (tensorPair ψ ket0))) ket0)

/-- Dopo `CNOT` su `|ψ⟩ ⊗ |0⟩` la lettura è la regola di Lüders.

`condition 0` è `(α, 0)` e `condition 1` è `(0, β)`. Le norme sono
`bornPair ψ`: il peso dell'esito è il peso di Born del sistema.
L'aggiornamento è questo teorema, nell'anello libero. -/
theorem luders (ψ : Pair) :
    condition 0 (applyCNOT (tensorPair ψ ket0)) = ⟨ψ.a0, []⟩ ∧
      condition 1 (applyCNOT (tensorPair ψ ket0)) = ⟨[], ψ.a1⟩ ∧
        pairSame ⟨normPair (condition 0 (applyCNOT (tensorPair ψ ket0))),
            normPair (condition 1 (applyCNOT (tensorPair ψ ket0)))⟩
          (bornPair ψ) := by
  rw [cnot_ket0]
  refine ⟨rfl, rfl, ?_⟩
  simp only [condition, normPair, bornPair, columnBorn_nil, List.append_nil, List.nil_append]
  exact ⟨polySame_refl _, polySame_refl _⟩

/-- Una seconda lettura, su un apparato fresco, ripete l'esito.

`CNOT` applicato a `condition k` con l'apparato in `|0⟩` dà, sul
puntatore, peso uguale alla norma di quello stato per l'esito `k` e
peso zero per l'altro. -/
theorem repeatable (ψ : Pair) :
    (polySame (marginalRight (reread 0 ψ)).a0
        (normPair (condition 0 (applyCNOT (tensorPair ψ ket0)))) ∧
      polySame (marginalRight (reread 0 ψ)).a1 []) ∧
      (polySame (marginalRight (reread 1 ψ)).a1
          (normPair (condition 1 (applyCNOT (tensorPair ψ ket0)))) ∧
        polySame (marginalRight (reread 1 ψ)).a0 []) := by
  unfold reread
  rw [cnot_ket0]
  simp only [condition]
  rw [tensor_idle_right, tensor_idle_right]
  simp only [applyCNOT, marginalRight, normPair, columnBorn_nil, List.append_nil,
    List.nil_append]
  exact ⟨⟨polySame_refl _, polySame_refl _⟩, ⟨polySame_refl _, polySame_refl _⟩⟩

/-- Nel punto `c = 3/5`, `s = 4/5`, `n = e_x` lo stato condizionato è
`3/5 |0⟩` oppure `−4/5 i |1⟩`. Le norme sono `9/25` e `16/25`. -/
theorem point_luders :
    evalAt pointC pointS 1 0 0
        (specPoly keepX
          (condition 0 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))).a0) =
      pointAlpha ∧
      evalAt pointC pointS 1 0 0
          (specPoly keepX
            (condition 0 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))).a1) = 0 ∧
        evalAt pointC pointS 1 0 0
            (specPoly keepX
              (condition 1 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))).a0) = 0 ∧
          evalAt pointC pointS 1 0 0
              (specPoly keepX
                (condition 1 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))).a1) =
            pointBeta ∧
            evalAt pointC pointS 1 0 0
                (specPoly keepX
                  (normPair
                    (condition 0 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))))) =
              ⟨(9 : Rat) / 25, 0⟩ ∧
              evalAt pointC pointS 1 0 0
                  (specPoly keepX
                    (normPair
                      (condition 1
                        (applyCNOT (tensorPair (applyMat evolution ket0) ket0))))) =
                ⟨(16 : Rat) / 25, 0⟩ := by
  have hket : applyMat evolution ket0 = ⟨evolution.a00, evolution.a10⟩ := by
    simp only [applyMat, ket0, pmul_one, pmul_nil, List.append_nil]
  have hv : applyCNOT (tensorPair (applyMat evolution ket0) ket0) =
      ⟨evolution.a00, [], [], evolution.a10⟩ := by
    rw [cnot_ket0, hket]
  simp only [hv, condition, normPair, columnBorn_nil, List.append_nil, List.nil_append]
  refine ⟨point_alpha, ?_, ?_, point_beta, ?_, ?_⟩
  · simp [specPoly, evalAt]
  · simp [specPoly, evalAt]
  · rw [eval_polySame (spec_columnBorn keepX_mul evolution.a00)]
    exact point_prob0
  · rw [eval_polySame (spec_columnBorn keepX_mul evolution.a10)]
    exact point_prob1

/-- Nello stesso punto la seconda lettura pesa `9/25` o `16/25`.
L'altro esito pesa `0`. -/
theorem point_repeatable :
    evalAt pointC pointS 1 0 0
        (specPoly keepX (marginalRight (reread 0 (applyMat evolution ket0))).a0) =
      ⟨(9 : Rat) / 25, 0⟩ ∧
      evalAt pointC pointS 1 0 0
          (specPoly keepX (marginalRight (reread 0 (applyMat evolution ket0))).a1) = 0 ∧
        evalAt pointC pointS 1 0 0
            (specPoly keepX (marginalRight (reread 1 (applyMat evolution ket0))).a0) = 0 ∧
          evalAt pointC pointS 1 0 0
              (specPoly keepX (marginalRight (reread 1 (applyMat evolution ket0))).a1) =
            ⟨(16 : Rat) / 25, 0⟩ := by
  have hket : applyMat evolution ket0 = ⟨evolution.a00, evolution.a10⟩ := by
    simp only [applyMat, ket0, pmul_one, pmul_nil, List.append_nil]
  unfold reread
  rw [cnot_ket0, hket]
  simp only [condition, tensor_idle_right, applyCNOT, marginalRight, columnBorn_nil,
    List.append_nil, List.nil_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eval_polySame (spec_columnBorn keepX_mul evolution.a00)]
    exact point_prob0
  · simp [specPoly, evalAt]
  · simp [specPoly, evalAt]
  · rw [eval_polySame (spec_columnBorn keepX_mul evolution.a10)]
    exact point_prob1

end Universe.Interaction
