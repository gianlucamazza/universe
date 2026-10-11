/-
Simmetrie della legge.

`U = c I − i s H` commuta con `H` nell'anello libero: `UH` e `HU` sono
entrambi `c H − i s H²`. L'energia `⟨ψ|H|ψ⟩` è conservata. La differenza
dopo `Φ` sta in `(gC, gN)`, perché `U†HU = U†UH` e `U†U − I` è `δ`.
Nel punto `c = 3/5`, `s = 4/5`, `⟨0|H|0⟩` vale `0` lungo `e_x` e `1`
lungo `e_z`, prima e dopo l'evoluzione.

Un `V` con `V†V = I` nell'anello libero porta la legge in `V U V†`:
`V (U ψ)` e `(V U V†) (V ψ)` hanno gli stessi coefficienti. I pesi di
Born di `Vψ` nella base `V|k⟩` sono quelli di `ψ`. `V V† = I` rende il
cambio invertibile. Nel punto `c = 3/5`, `s = 4/5`, `n = e_x` quella
matrice dà `V(U|0⟩) = −7/25 |0⟩ − 24/25 i |1⟩`, con pesi `1` e `0`.
-/
import Universe.Composition
import Universe.Evaluation
import Universe.Qubit

namespace Universe.Symmetry

open Universe.Ring
open Universe.Quotient hiding mul
open Universe.Dynamics
open Universe.Qubit
open Universe.Epistemology
open Universe.Evaluation
open Universe.Composition

theorem pairSame_symm {ψ φ : Pair} (h : pairSame ψ φ) : pairSame φ ψ :=
  ⟨h.1.symm, h.2.symm⟩

theorem apply_assoc (A B : Mat) (α β : Poly) :
    pairSame (applyMat (matMul A B) ⟨α, β⟩) (applyMat A (applyMat B ⟨α, β⟩)) := by
  refine ⟨?_, ?_⟩
  · simpa only [applyMat, matMul] using
      polySame_assoc_col A.a00 A.a01 B.a00 B.a01 B.a10 B.a11 α β
  · simpa only [applyMat, matMul] using
      polySame_assoc_col A.a10 A.a11 B.a00 B.a01 B.a10 B.a11 α β

/-- `(p + q a) x + (q b) y` e `p x + q (a x + b y)`. -/
theorem polySame_lin_row (p q a b x y : Poly) :
    polySame (pmul (p ++ pmul q a) x ++ pmul (pmul q b) y)
      (pmul p x ++ pmul q (pmul a x ++ pmul b y)) := by
  intro t
  calc
    coeffOf (pmul (p ++ pmul q a) x ++ pmul (pmul q b) y) t
        = coeffOf ((pmul p x ++ pmul q (pmul a x)) ++ pmul q (pmul b y)) t := by
          rw [pmul_append_left, pmul_assoc, pmul_assoc]
    _ = coeffOf (pmul p x ++ (pmul q (pmul a x) ++ pmul q (pmul b y))) t :=
          polySame_append_assoc _ _ _ t
    _ = coeffOf (pmul p x ++ pmul q (pmul a x ++ pmul b y)) t := by
          rw [coeffOf_append, (polySame_mul_append_right q (pmul a x) (pmul b y)).symm t,
            ← coeffOf_append]

/-- Lo stesso prodotto con `p` sul secondo addendo. -/
theorem polySame_lin_row_swap (p q a b x y : Poly) :
    polySame (pmul (pmul q a) x ++ pmul (p ++ pmul q b) y)
      (pmul p y ++ pmul q (pmul a x ++ pmul b y)) := by
  intro t
  calc
    coeffOf (pmul (pmul q a) x ++ pmul (p ++ pmul q b) y) t
        = coeffOf (pmul q (pmul a x)) t + coeffOf (pmul (p ++ pmul q b) y) t := by
          rw [pmul_assoc, coeffOf_append]
    _ = coeffOf (pmul q (pmul a x)) t +
          (coeffOf (pmul p y) t + coeffOf (pmul (pmul q b) y) t) := by
          rw [pmul_append_left, coeffOf_append]
    _ = coeffOf (pmul q (pmul a x)) t +
          (coeffOf (pmul p y) t + coeffOf (pmul q (pmul b y)) t) := by
          rw [pmul_assoc]
    _ = coeffOf (pmul p y) t +
          (coeffOf (pmul q (pmul a x)) t + coeffOf (pmul q (pmul b y)) t) :=
          gauss_rot _ _ _
    _ = coeffOf (pmul p y) t + coeffOf (pmul q (pmul a x) ++ pmul q (pmul b y)) t := by
          rw [← coeffOf_append]
    _ = coeffOf (pmul p y) t + coeffOf (pmul q (pmul a x ++ pmul b y)) t := by
          rw [(polySame_mul_append_right q (pmul a x) (pmul b y)).symm t]
    _ = coeffOf (pmul p y ++ pmul q (pmul a x ++ pmul b y)) t := by
          rw [← coeffOf_append]

/-- `a (p + q x) + b (q y)` e `p a + q (a x + b y)`. -/
theorem polySame_row_lin (p q a b x y : Poly) :
    polySame (pmul a (p ++ pmul q x) ++ pmul b (pmul q y))
      (pmul p a ++ pmul q (pmul a x ++ pmul b y)) := by
  intro t
  calc
    coeffOf (pmul a (p ++ pmul q x) ++ pmul b (pmul q y)) t
        = coeffOf (pmul a (p ++ pmul q x)) t + coeffOf (pmul b (pmul q y)) t := by
          rw [coeffOf_append]
    _ = coeffOf (pmul a p ++ pmul a (pmul q x)) t + coeffOf (pmul b (pmul q y)) t := by
          rw [(polySame_mul_append_right a p (pmul q x)) t]
    _ = (coeffOf (pmul p a) t + coeffOf (pmul q (pmul a x)) t) +
          coeffOf (pmul q (pmul b y)) t := by
          rw [coeffOf_append, (polySame_mul_comm a p) t, (slide_right a q x) t,
            (slide_right b q y) t]
    _ = coeffOf (pmul p a) t +
          (coeffOf (pmul q (pmul a x)) t + coeffOf (pmul q (pmul b y)) t) := by
          rw [Gauss.add_assoc]
    _ = coeffOf (pmul p a) t + coeffOf (pmul q (pmul a x ++ pmul b y)) t := by
          rw [← coeffOf_append, (polySame_mul_append_right q (pmul a x) (pmul b y)).symm t]
    _ = coeffOf (pmul p a ++ pmul q (pmul a x ++ pmul b y)) t := by
          rw [← coeffOf_append]

/-- Lo stesso prodotto con `p` sul secondo addendo. -/
theorem polySame_row_lin_swap (p q a b x y : Poly) :
    polySame (pmul a (pmul q x) ++ pmul b (p ++ pmul q y))
      (pmul p b ++ pmul q (pmul a x ++ pmul b y)) := by
  intro t
  calc
    coeffOf (pmul a (pmul q x) ++ pmul b (p ++ pmul q y)) t
        = coeffOf (pmul a (pmul q x)) t + coeffOf (pmul b (p ++ pmul q y)) t := by
          rw [coeffOf_append]
    _ = coeffOf (pmul q (pmul a x)) t + coeffOf (pmul b p ++ pmul b (pmul q y)) t := by
          rw [(slide_right a q x) t, (polySame_mul_append_right b p (pmul q y)) t]
    _ = coeffOf (pmul q (pmul a x)) t +
          (coeffOf (pmul p b) t + coeffOf (pmul q (pmul b y)) t) := by
          rw [coeffOf_append, (polySame_mul_comm b p) t, (slide_right b q y) t]
    _ = coeffOf (pmul p b) t +
          (coeffOf (pmul q (pmul a x)) t + coeffOf (pmul q (pmul b y)) t) :=
          gauss_rot _ _ _
    _ = coeffOf (pmul p b ++ pmul q (pmul a x ++ pmul b y)) t := by
          rw [← coeffOf_append, (polySame_mul_append_right q (pmul a x) (pmul b y)).symm t,
            ← coeffOf_append]

/-- `p H + q H²`. Con `p = c` e `q = −i s` è `c H − i s H²`. -/
def motion (p q : Poly) (H : Mat) : Mat :=
  matAdd (matScale p H) (matScale q (matMul H H))

theorem motion_a00 (p q : Poly) (H : Mat) :
    (motion p q H).a00 = pmul p H.a00 ++ pmul q (pmul H.a00 H.a00 ++ pmul H.a01 H.a10) := by
  unfold motion matAdd matScale matMul
  rfl

theorem motion_a01 (p q : Poly) (H : Mat) :
    (motion p q H).a01 = pmul p H.a01 ++ pmul q (pmul H.a00 H.a01 ++ pmul H.a01 H.a11) := by
  unfold motion matAdd matScale matMul
  rfl

theorem motion_a10 (p q : Poly) (H : Mat) :
    (motion p q H).a10 = pmul p H.a10 ++ pmul q (pmul H.a10 H.a00 ++ pmul H.a11 H.a10) := by
  unfold motion matAdd matScale matMul
  rfl

theorem motion_a11 (p q : Poly) (H : Mat) :
    (motion p q H).a11 = pmul p H.a11 ++ pmul q (pmul H.a10 H.a01 ++ pmul H.a11 H.a11) := by
  unfold motion matAdd matScale matMul
  rfl

theorem lin_a00 (p q : Poly) (H : Mat) : (lin p q H).a00 = p ++ pmul q H.a00 := by
  simp only [lin, pmul_one]

theorem lin_a11 (p q : Poly) (H : Mat) : (lin p q H).a11 = p ++ pmul q H.a11 := by
  simp only [lin, pmul_one]

/-- `(p I + q H) H` ha i coefficienti di `p H + q H²`. -/
theorem lin_motion (p q : Poly) (H : Mat) : matSame (matMul (lin p q H) H) (motion p q H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    rw [show (matMul (lin p q H) H).a00 =
          pmul (lin p q H).a00 H.a00 ++ pmul (lin p q H).a01 H.a10 from rfl,
        lin_a00, show (lin p q H).a01 = pmul q H.a01 from rfl, motion_a00]
    exact polySame_lin_row p q H.a00 H.a01 H.a00 H.a10 t
  · intro t
    rw [show (matMul (lin p q H) H).a01 =
          pmul (lin p q H).a00 H.a01 ++ pmul (lin p q H).a01 H.a11 from rfl,
        lin_a00, show (lin p q H).a01 = pmul q H.a01 from rfl, motion_a01]
    exact polySame_lin_row p q H.a00 H.a01 H.a01 H.a11 t
  · intro t
    rw [show (matMul (lin p q H) H).a10 =
          pmul (lin p q H).a10 H.a00 ++ pmul (lin p q H).a11 H.a10 from rfl,
        show (lin p q H).a10 = pmul q H.a10 from rfl, lin_a11, motion_a10]
    exact polySame_lin_row_swap p q H.a10 H.a11 H.a00 H.a10 t
  · intro t
    rw [show (matMul (lin p q H) H).a11 =
          pmul (lin p q H).a10 H.a01 ++ pmul (lin p q H).a11 H.a11 from rfl,
        show (lin p q H).a10 = pmul q H.a10 from rfl, lin_a11, motion_a11]
    exact polySame_lin_row_swap p q H.a10 H.a11 H.a01 H.a11 t

/-- `H (p I + q H)` ha gli stessi coefficienti. -/
theorem motion_lin (p q : Poly) (H : Mat) : matSame (matMul H (lin p q H)) (motion p q H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    rw [show (matMul H (lin p q H)).a00 =
          pmul H.a00 (lin p q H).a00 ++ pmul H.a01 (lin p q H).a10 from rfl,
        lin_a00, show (lin p q H).a10 = pmul q H.a10 from rfl, motion_a00]
    exact polySame_row_lin p q H.a00 H.a01 H.a00 H.a10 t
  · intro t
    rw [show (matMul H (lin p q H)).a01 =
          pmul H.a00 (lin p q H).a01 ++ pmul H.a01 (lin p q H).a11 from rfl,
        show (lin p q H).a01 = pmul q H.a01 from rfl, lin_a11, motion_a01]
    exact polySame_row_lin_swap p q H.a00 H.a01 H.a01 H.a11 t
  · intro t
    rw [show (matMul H (lin p q H)).a10 =
          pmul H.a10 (lin p q H).a00 ++ pmul H.a11 (lin p q H).a10 from rfl,
        lin_a00, show (lin p q H).a10 = pmul q H.a10 from rfl, motion_a10]
    exact polySame_row_lin p q H.a10 H.a11 H.a00 H.a10 t
  · intro t
    rw [show (matMul H (lin p q H)).a11 =
          pmul H.a10 (lin p q H).a01 ++ pmul H.a11 (lin p q H).a11 from rfl,
        show (lin p q H).a01 = pmul q H.a01 from rfl, lin_a11, motion_a11]
    exact polySame_row_lin_swap p q H.a10 H.a11 H.a01 H.a11 t

/-- `UH` e `HU` hanno gli stessi coefficienti. Entrambi sono `c H − i s H²`. -/
theorem evolution_commutes_hamiltonian :
    matSame (matMul evolution hamiltonian) (matMul hamiltonian evolution) := by
  rw [evolution]
  exact matSame_trans (lin_motion cP gamma hamiltonian)
    (matSame_symm (motion_lin cP gamma hamiltonian))

theorem polySame_bra_term (u a x : Poly) :
    polySame (pmul (pmul (conjP u) (conjP a)) x) (pmul (conjP a) (pmul (conjP u) x)) := by
  intro t
  rw [pmul_assoc]
  exact slide_right (conjP u) (conjP a) x t

/-- `⟨Uψ|ξ⟩` e `⟨ψ|U† ξ⟩` hanno gli stessi coefficienti. -/
theorem bra_pull (u00 u01 u10 u11 α β x y : Poly) :
    polySame
      (pmul (conjP (pmul u00 α ++ pmul u01 β)) x ++
        pmul (conjP (pmul u10 α ++ pmul u11 β)) y)
      (pmul (conjP α) (pmul (conjP u00) x ++ pmul (conjP u10) y) ++
        pmul (conjP β) (pmul (conjP u01) x ++ pmul (conjP u11) y)) := by
  intro t
  rw [conj_append, conj_append, conj_pmul, conj_pmul, conj_pmul, conj_pmul, pmul_append_left,
    pmul_append_left]
  have hmove :=
    polySame_append
      (polySame_append (polySame_bra_term u00 α x) (polySame_bra_term u01 β x))
      (polySame_append (polySame_bra_term u10 α y) (polySame_bra_term u11 β y))
  calc
    coeffOf
          ((pmul (pmul (conjP u00) (conjP α)) x ++ pmul (pmul (conjP u01) (conjP β)) x) ++
            (pmul (pmul (conjP u10) (conjP α)) y ++ pmul (pmul (conjP u11) (conjP β)) y))
          t
        = coeffOf
            ((pmul (conjP α) (pmul (conjP u00) x) ++ pmul (conjP β) (pmul (conjP u01) x)) ++
              (pmul (conjP α) (pmul (conjP u10) y) ++ pmul (conjP β) (pmul (conjP u11) y)))
            t :=
          hmove t
    _ = coeffOf
            ((pmul (conjP α) (pmul (conjP u00) x) ++ pmul (conjP α) (pmul (conjP u10) y)) ++
              (pmul (conjP β) (pmul (conjP u01) x) ++ pmul (conjP β) (pmul (conjP u11) y)))
            t :=
          polySame_append4_mid _ _ _ _ t
    _ = coeffOf
            (pmul (conjP α) (pmul (conjP u00) x ++ pmul (conjP u10) y) ++
              pmul (conjP β) (pmul (conjP u01) x ++ pmul (conjP u11) y))
            t := by
          rw [coeffOf_append,
            (polySame_mul_append_right (conjP α) (pmul (conjP u00) x) (pmul (conjP u10) y)).symm t,
            (polySame_mul_append_right (conjP β) (pmul (conjP u01) x) (pmul (conjP u11) y)).symm t,
            ← coeffOf_append]

theorem sandwich_as_bra (M : Mat) (ψ : Pair) :
    sandwich M ψ.a0 ψ.a1 =
      pmul (conjP ψ.a0) (applyMat M ψ).a0 ++ pmul (conjP ψ.a1) (applyMat M ψ).a1 :=
  rfl

theorem sandwich_components (M : Mat) (α β : Poly) :
    sandwich M α β =
      pmul (conjP α) (applyMat M ⟨α, β⟩).a0 ++ pmul (conjP β) (applyMat M ⟨α, β⟩).a1 :=
  rfl

/-- `⟨Uψ|M|Uψ⟩` e `⟨ψ|U† M U|ψ⟩` hanno gli stessi coefficienti. -/
theorem sandwich_conj (M U : Mat) (α β : Poly) :
    polySame (sandwich M (applyMat U ⟨α, β⟩).a0 (applyMat U ⟨α, β⟩).a1)
      (sandwich (matMul (matDagger U) (matMul M U)) α β) := by
  let φ : Pair := applyMat U ⟨α, β⟩
  let mid : Pair := applyMat (matMul M U) ⟨α, β⟩
  have hket : pairSame (applyMat M φ) mid := pairSame_symm (apply_assoc M U α β)
  have hbra : polySame (sandwich M φ.a0 φ.a1)
      (pmul (conjP φ.a0) mid.a0 ++ pmul (conjP φ.a1) mid.a1) := by
    rw [sandwich_as_bra M φ]
    exact polySame_append (polySame_pmul_right hket.1 (conjP φ.a0))
      (polySame_pmul_right hket.2 (conjP φ.a1))
  have hpull : polySame (pmul (conjP φ.a0) mid.a0 ++ pmul (conjP φ.a1) mid.a1)
      (pmul (conjP α) (applyMat (matDagger U) mid).a0 ++
        pmul (conjP β) (applyMat (matDagger U) mid).a1) := by
    rw [show φ.a0 = pmul U.a00 α ++ pmul U.a01 β from rfl,
      show φ.a1 = pmul U.a10 α ++ pmul U.a11 β from rfl,
      show (applyMat (matDagger U) mid).a0 =
        pmul (conjP U.a00) mid.a0 ++ pmul (conjP U.a10) mid.a1 from rfl,
      show (applyMat (matDagger U) mid).a1 =
        pmul (conjP U.a01) mid.a0 ++ pmul (conjP U.a11) mid.a1 from rfl]
    exact bra_pull U.a00 U.a01 U.a10 U.a11 α β mid.a0 mid.a1
  have hlast : pairSame (applyMat (matDagger U) mid)
      (applyMat (matMul (matDagger U) (matMul M U)) ⟨α, β⟩) :=
    pairSame_symm (apply_assoc (matDagger U) (matMul M U) α β)
  have hfin : polySame
      (pmul (conjP α) (applyMat (matDagger U) mid).a0 ++
        pmul (conjP β) (applyMat (matDagger U) mid).a1)
      (sandwich (matMul (matDagger U) (matMul M U)) α β) := by
    rw [sandwich_components (matMul (matDagger U) (matMul M U)) α β]
    exact polySame_append (polySame_pmul_right hlast.1 (conjP α))
      (polySame_pmul_right hlast.2 (conjP β))
  intro t
  exact ((hbra t).trans (hpull t)).trans (hfin t)

theorem sandwich_matSame {M N : Mat} (h : matSame M N) (α β : Poly) :
    polySame (sandwich M α β) (sandwich N α β) := by
  intro t
  rw [sandwich, sandwich]
  exact polySame_append
    (polySame_pmul_right
      (polySame_append (polySame_pmul_left h.1 α) (polySame_pmul_left h.2.1 β)) (conjP α))
    (polySame_pmul_right
      (polySame_append (polySame_pmul_left h.2.2.1 α) (polySame_pmul_left h.2.2.2 β))
      (conjP β)) t

theorem sandwich_rel {M N : Mat} (h : matRel M N) (α β : Poly) :
    inIdeal (psub (sandwich M α β) (sandwich N α β)) := by
  have row0 : inIdeal (psub (pmul M.a00 α ++ pmul M.a01 β) (pmul N.a00 α ++ pmul N.a01 β)) :=
    inIdeal_dot_left M.a00 N.a00 M.a01 N.a01 α β h.1 h.2.1
  have row1 : inIdeal (psub (pmul M.a10 α ++ pmul M.a11 β) (pmul N.a10 α ++ pmul N.a11 β)) :=
    inIdeal_dot_left M.a10 N.a10 M.a11 N.a11 α β h.2.2.1 h.2.2.2
  have bra0 : inIdeal
      (psub (pmul (conjP α) (pmul M.a00 α ++ pmul M.a01 β))
        (pmul (conjP α) (pmul N.a00 α ++ pmul N.a01 β))) :=
    inIdeal_polySame (polySame.symm (polySame_mul_psub_right (conjP α) _ _))
      (inIdeal_mul_left (conjP α) row0)
  have bra1 : inIdeal
      (psub (pmul (conjP β) (pmul M.a10 α ++ pmul M.a11 β))
        (pmul (conjP β) (pmul N.a10 α ++ pmul N.a11 β))) :=
    inIdeal_polySame (polySame.symm (polySame_mul_psub_right (conjP β) _ _))
      (inIdeal_mul_left (conjP β) row1)
  exact inIdeal_polySame (polySame_psub_append _ _ _ _) (inIdeal_append bra0 bra1)

/-- `⟨Uψ|H|Uψ⟩ − ⟨ψ|H|ψ⟩` sta in `(gC, gN)`, per ogni ampiezza.
`U†HU = U†UH` per la commutazione, e `U†U − I` è `δ`. -/
theorem energy_conserved (α β : Poly) :
    inIdeal
      (psub (sandwich hamiltonian (applyMat evolution ⟨α, β⟩).a0 (applyMat evolution ⟨α, β⟩).a1)
        (sandwich hamiltonian α β)) := by
  have hcomm : matSame (matMul hamiltonian evolution) (matMul evolution hamiltonian) :=
    matSame_symm evolution_commutes_hamiltonian
  have hpass : matSame (matMul (matDagger evolution) (matMul hamiltonian evolution))
      (matMul (matDagger evolution) (matMul evolution hamiltonian)) :=
    matSame_mul_right (matDagger evolution) hcomm
  have hassoc : matSame (matMul (matDagger evolution) (matMul evolution hamiltonian))
      (matMul (matMul (matDagger evolution) evolution) hamiltonian) :=
    matSame_symm (matMul_assoc (matDagger evolution) evolution hamiltonian)
  have hform := matSame_trans hpass hassoc
  have hunit : matRel (matMul (matMul (matDagger evolution) evolution) hamiltonian) hamiltonian := by
    simpa only [matMul_one_left] using matMul_left_rel evolution_unitary hamiltonian
  exact inIdeal_polySame
    (polySame_psub
      (polySame.trans (sandwich_conj hamiltonian evolution α β) (sandwich_matSame hform α β))
      (polySame_refl _))
    (sandwich_rel hunit α β)

theorem energy_at (α β : Poly) (nx ny nz : Rat) (hc : evalAt pointC pointS nx ny nz gC = 0)
    (hn : evalAt pointC pointS nx ny nz gN = 0) :
    evalAt pointC pointS nx ny nz
        (sandwich hamiltonian (applyMat evolution ⟨α, β⟩).a0 (applyMat evolution ⟨α, β⟩).a1) =
      evalAt pointC pointS nx ny nz (sandwich hamiltonian α β) := by
  have hzero := eval_inIdeal (energy_conserved α β) pointC pointS nx ny nz hc hn
  have hsub :=
    eval_psub pointC pointS nx ny nz
      (sandwich hamiltonian (applyMat evolution ⟨α, β⟩).a0 (applyMat evolution ⟨α, β⟩).a1)
      (sandwich hamiltonian α β)
  exact gauss_of_sub _ _ (hsub.symm.trans hzero)

theorem sandwich_ket0 (M : Mat) : sandwich M ket0.a0 ket0.a1 = M.a00 := by
  simp only [sandwich, ket0, conjP_real, pmul_one, pmul_nil, one_pmul, pmul_nil_left,
    List.append_nil, conjP]

theorem h00_at (nx ny nz : Rat) :
    evalAt pointC pointS nx ny nz (sandwich hamiltonian ket0.a0 ket0.a1) = ⟨nz, 0⟩ := by
  rw [sandwich_ket0, show hamiltonian.a00 = single (1 : Gauss) nz1 from rfl, eval_single]
  ext <;> simp [monoVal, powR, nz1, pointC, pointS]

theorem circle_at_point (nx ny nz : Rat) : evalAt pointC pointS nx ny nz gC = 0 := by
  rw [gC, eval_append, eval_append, eval_single, eval_single, eval_single]
  simp [monoVal, powR, cSq, sSq, pointC, pointS]
  ext <;> simp <;> grind

theorem sphere_at_z : evalAt pointC pointS 0 0 1 gN = 0 := by
  rw [gN, eval_append, eval_append, eval_append, eval_single, eval_single, eval_single,
    eval_single]
  simp [monoVal, powR, nxSq, nySq, nzSq, pointC, pointS]
  ext <;> simp <;> grind

theorem applyMat_proj (U : Mat) (ψ : Pair) : applyMat U ⟨ψ.a0, ψ.a1⟩ = applyMat U ψ := rfl

/-- Nel punto `c = 3/5`, `s = 4/5`, `n = e_x`, `⟨0|H|0⟩ = ⟨U0|H|U0⟩ = 0`. -/
theorem point_energy_x :
    evalAt pointC pointS 1 0 0 (sandwich hamiltonian ket0.a0 ket0.a1) = 0 ∧
      evalAt pointC pointS 1 0 0
          (sandwich hamiltonian (applyMat evolution ket0).a0 (applyMat evolution ket0).a1) =
        0 := by
  refine ⟨?_, ?_⟩
  · rw [h00_at]
    ext <;> simp
  · rw [← applyMat_proj evolution ket0, energy_at ket0.a0 ket0.a1 1 0 0 point_gC point_gN, h00_at]
    ext <;> simp

/-- Sullo stesso cerchio, lungo `n = e_z`, `⟨0|H|0⟩ = ⟨U0|H|U0⟩ = 1`. -/
theorem point_energy_z :
    evalAt pointC pointS 0 0 1 (sandwich hamiltonian ket0.a0 ket0.a1) = 1 ∧
      evalAt pointC pointS 0 0 1
          (sandwich hamiltonian (applyMat evolution ket0).a0 (applyMat evolution ket0).a1) =
        1 := by
  refine ⟨?_, ?_⟩
  · rw [h00_at]
    ext <;> simp
  · rw [← applyMat_proj evolution ket0,
      energy_at ket0.a0 ket0.a1 0 0 1 (circle_at_point 0 0 1) sphere_at_z, h00_at]
    ext <;> simp

/-! ### Cambio di base -/

/-- `⟨φ|ξ⟩`. -/
def braket (φ ξ : Pair) : Poly :=
  pmul (conjP φ.a0) ξ.a0 ++ pmul (conjP φ.a1) ξ.a1

/-- Colonna `k`, lo stato `M|k⟩`. -/
def matColumn (M : Mat) : Fin 2 → Pair
  | 0 => ⟨M.a00, M.a10⟩
  | 1 => ⟨M.a01, M.a11⟩

theorem braket_dagger (M : Mat) (ξ : Pair) :
    braket (matColumn M 0) ξ = (applyMat (matDagger M) ξ).a0 ∧
      braket (matColumn M 1) ξ = (applyMat (matDagger M) ξ).a1 := by
  constructor <;> rfl

/-- `A (B ψ) = ψ` quando `AB = I` nell'anello libero. -/
theorem apply_cancel (A B : Mat) (ψ : Pair) (h : matSame (matMul A B) matOne) :
    pairSame (applyMat A (applyMat B ψ)) ψ := by
  have hstep : pairSame (applyMat A (applyMat B ψ)) (applyMat (matMul A B) ψ) :=
    pairSame_symm (apply_assoc A B ψ.a0 ψ.a1)
  have hunit : pairSame (applyMat (matMul A B) ψ) (applyMat matOne ψ) :=
    apply_matSame h ψ
  exact pairSame.trans hstep (pairSame.trans hunit (by
    rw [applyMat_one]
    exact pairSame_refl ψ))

/-- `V (U ψ)` e `(V U V†) (V ψ)` hanno gli stessi coefficienti
quando `V† V = I` nell'anello libero. -/
theorem conj_evolution (V U : Mat) (ψ : Pair)
    (h : matSame (matMul (matDagger V) V) matOne) :
    pairSame (applyMat V (applyMat U ψ))
      (applyMat (matMul (matMul V U) (matDagger V)) (applyMat V ψ)) := by
  have hback : pairSame (applyMat (matDagger V) (applyMat V ψ)) ψ :=
    apply_cancel (matDagger V) V ψ h
  have hmid : pairSame
      (applyMat (matMul V U) (applyMat (matDagger V) (applyMat V ψ)))
      (applyMat (matMul V U) ψ) :=
    apply_pairSame (matMul V U) hback
  have houter : pairSame
      (applyMat (matMul (matMul V U) (matDagger V)) (applyMat V ψ))
      (applyMat (matMul V U) (applyMat (matDagger V) (applyMat V ψ))) :=
    apply_assoc (matMul V U) (matDagger V) (applyMat V ψ).a0 (applyMat V ψ).a1
  have hinner : pairSame (applyMat (matMul V U) ψ) (applyMat V (applyMat U ψ)) :=
    apply_assoc V U ψ.a0 ψ.a1
  exact pairSame_symm (pairSame.trans houter (pairSame.trans hmid hinner))

/-- I pesi di Born di `Vψ` nella base `V|k⟩` sono quelli di `ψ`. -/
theorem conj_born (V : Mat) (ψ : Pair)
    (h : matSame (matMul (matDagger V) V) matOne) :
    polySame (columnBorn (braket (matColumn V 0) (applyMat V ψ))) (columnBorn ψ.a0) ∧
      polySame (columnBorn (braket (matColumn V 1) (applyMat V ψ))) (columnBorn ψ.a1) := by
  have hstate : pairSame (applyMat (matDagger V) (applyMat V ψ)) ψ :=
    apply_cancel (matDagger V) V ψ h
  have hcols := braket_dagger V (applyMat V ψ)
  refine ⟨?_, ?_⟩
  · rw [hcols.1]
    exact polySame_columnBorn hstate.1
  · rw [hcols.2]
    exact polySame_columnBorn hstate.2

/-- `V V† = I` nell'anello libero: `V (V† φ) = φ`. -/
theorem conj_inverse (V : Mat) (φ : Pair)
    (h : matSame (matMul V (matDagger V)) matOne) :
    pairSame (applyMat V (applyMat (matDagger V) φ)) φ :=
  apply_cancel V (matDagger V) φ h

/-! ### Il punto `c = 3/5`, `s = 4/5` come matrice -/

def basisReal : Gauss := ⟨pointC, 0⟩

def basisImag : Gauss := ⟨0, -pointS⟩

/-- `U` nel punto `n = e_x`: `[[3/5, −4/5 i], [−4/5 i, 3/5]]`. -/
def pointBasis : Mat where
  a00 := single basisReal Mono.one
  a01 := single basisImag Mono.one
  a10 := single basisImag Mono.one
  a11 := single basisReal Mono.one

theorem basis_conj_real : Gauss.conj basisReal = basisReal := by
  ext <;> simp [Gauss.conj, basisReal]

theorem basis_diag :
    basisReal * basisReal + Gauss.conj basisImag * basisImag = 1 := by
  ext <;> simp [basisReal, basisImag, Gauss.conj, pointC, pointS] <;> grind

theorem basis_off :
    basisReal * basisImag + Gauss.conj basisImag * basisReal = 0 := by
  ext <;> simp [basisReal, basisImag, Gauss.conj, pointC, pointS] <;> grind

theorem basis_off_rev :
    basisReal * Gauss.conj basisImag + basisImag * basisReal = 0 := by
  ext <;> simp [basisReal, basisImag, Gauss.conj, pointC, pointS] <;> grind

theorem basis_norm :
    basisReal * basisReal + basisImag * Gauss.conj basisImag = 1 := by
  rw [Gauss.mul_comm basisImag (Gauss.conj basisImag), basis_diag]

theorem basis_diag_swap :
    Gauss.conj basisImag * basisImag + basisReal * basisReal = 1 := by
  rw [Gauss.add_comm, basis_diag]

theorem basis_off_swap :
    Gauss.conj basisImag * basisReal + basisReal * basisImag = 0 := by
  rw [Gauss.add_comm, basis_off]

theorem basis_off_rev_swap :
    basisImag * basisReal + basisReal * Gauss.conj basisImag = 0 := by
  rw [Gauss.add_comm, basis_off_rev]

theorem basis_norm_swap :
    basisImag * Gauss.conj basisImag + basisReal * basisReal = 1 := by
  rw [Gauss.add_comm, basis_norm]

theorem basis_square_0 :
    basisReal * basisReal + basisImag * basisImag = ⟨-(7 : Rat) / 25, 0⟩ := by
  ext <;> simp [basisReal, basisImag, pointC, pointS] <;> grind

theorem basis_square_1 :
    basisImag * basisReal + basisReal * basisImag = ⟨0, -(24 : Rat) / 25⟩ := by
  ext <;> simp [basisReal, basisImag, pointC, pointS] <;> grind

theorem point_dagger_a00 : (matDagger pointBasis).a00 = single basisReal Mono.one := by
  simp only [matDagger, pointBasis]
  rw [conjP_single, basis_conj_real]

theorem point_dagger_a01 :
    (matDagger pointBasis).a01 = single (Gauss.conj basisImag) Mono.one := by
  simp only [matDagger, pointBasis]
  rw [conjP_single]

theorem point_dagger_a10 :
    (matDagger pointBasis).a10 = single (Gauss.conj basisImag) Mono.one := by
  simp only [matDagger, pointBasis]
  rw [conjP_single]

theorem point_dagger_a11 : (matDagger pointBasis).a11 = single basisReal Mono.one := by
  simp only [matDagger, pointBasis]
  rw [conjP_single, basis_conj_real]

theorem point_basis_unitary : matSame (matMul (matDagger pointBasis) pointBasis) matOne := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (matMul (matDagger pointBasis) pointBasis).a00 =
        pmul (matDagger pointBasis).a00 pointBasis.a00 ++
          pmul (matDagger pointBasis).a01 pointBasis.a10 from rfl,
      point_dagger_a00, point_dagger_a01, pointBasis, matOne]
    exact polySame_const_dot _ _ _ _ _ basis_diag
  · rw [show (matMul (matDagger pointBasis) pointBasis).a01 =
        pmul (matDagger pointBasis).a00 pointBasis.a01 ++
          pmul (matDagger pointBasis).a01 pointBasis.a11 from rfl,
      point_dagger_a00, point_dagger_a01, pointBasis, matOne]
    exact polySame_const_dot_zero _ _ _ _ basis_off
  · rw [show (matMul (matDagger pointBasis) pointBasis).a10 =
        pmul (matDagger pointBasis).a10 pointBasis.a00 ++
          pmul (matDagger pointBasis).a11 pointBasis.a10 from rfl,
      point_dagger_a10, point_dagger_a11, pointBasis, matOne]
    exact polySame_const_dot_zero _ _ _ _ basis_off_swap
  · rw [show (matMul (matDagger pointBasis) pointBasis).a11 =
        pmul (matDagger pointBasis).a10 pointBasis.a01 ++
          pmul (matDagger pointBasis).a11 pointBasis.a11 from rfl,
      point_dagger_a10, point_dagger_a11, pointBasis, matOne]
    exact polySame_const_dot _ _ _ _ _ basis_diag_swap

theorem point_basis_unitary_rev :
    matSame (matMul pointBasis (matDagger pointBasis)) matOne := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (matMul pointBasis (matDagger pointBasis)).a00 =
        pmul pointBasis.a00 (matDagger pointBasis).a00 ++
          pmul pointBasis.a01 (matDagger pointBasis).a10 from rfl,
      point_dagger_a00, point_dagger_a10, pointBasis, matOne]
    exact polySame_const_dot _ _ _ _ _ basis_norm
  · rw [show (matMul pointBasis (matDagger pointBasis)).a01 =
        pmul pointBasis.a00 (matDagger pointBasis).a01 ++
          pmul pointBasis.a01 (matDagger pointBasis).a11 from rfl,
      point_dagger_a01, point_dagger_a11, pointBasis, matOne]
    exact polySame_const_dot_zero _ _ _ _ basis_off_rev
  · rw [show (matMul pointBasis (matDagger pointBasis)).a10 =
        pmul pointBasis.a10 (matDagger pointBasis).a00 ++
          pmul pointBasis.a11 (matDagger pointBasis).a10 from rfl,
      point_dagger_a00, point_dagger_a10, pointBasis, matOne]
    exact polySame_const_dot_zero _ _ _ _ basis_off_rev_swap
  · rw [show (matMul pointBasis (matDagger pointBasis)).a11 =
        pmul pointBasis.a10 (matDagger pointBasis).a01 ++
          pmul pointBasis.a11 (matDagger pointBasis).a11 from rfl,
      point_dagger_a01, point_dagger_a11, pointBasis, matOne]
    exact polySame_const_dot _ _ _ _ _ basis_norm_swap

theorem eval_apply_a0 (c s nx ny nz : Rat) (M : Mat) (ψ : Pair) :
    evalAt c s nx ny nz (applyMat M ψ).a0 =
      evalAt c s nx ny nz M.a00 * evalAt c s nx ny nz ψ.a0 +
        evalAt c s nx ny nz M.a01 * evalAt c s nx ny nz ψ.a1 := by
  rw [show (applyMat M ψ).a0 = pmul M.a00 ψ.a0 ++ pmul M.a01 ψ.a1 from rfl, eval_append,
    eval_pmul, eval_pmul]

theorem eval_apply_a1 (c s nx ny nz : Rat) (M : Mat) (ψ : Pair) :
    evalAt c s nx ny nz (applyMat M ψ).a1 =
      evalAt c s nx ny nz M.a10 * evalAt c s nx ny nz ψ.a0 +
        evalAt c s nx ny nz M.a11 * evalAt c s nx ny nz ψ.a1 := by
  rw [show (applyMat M ψ).a1 = pmul M.a10 ψ.a0 ++ pmul M.a11 ψ.a1 from rfl, eval_append,
    eval_pmul, eval_pmul]

theorem eval_evol_ket0_a0 :
    evalAt pointC pointS 1 0 0 (applyMat evolution ket0).a0 = basisReal := by
  have hket : (applyMat evolution ket0).a0 = evolution.a00 := by
    simp only [applyMat, ket0, pmul_one, pmul_nil, List.append_nil]
  rw [hket, eval_bracket_axis_x]
  ext <;> rfl

theorem eval_evol_ket0_a1 :
    evalAt pointC pointS 1 0 0 (applyMat evolution ket0).a1 = basisImag := by
  have hket : (applyMat evolution ket0).a1 = evolution.a10 := by
    simp only [applyMat, ket0, pmul_one, pmul_nil, List.append_nil]
  rw [hket, evolution_a10_bin, eval_append, eval_single, eval_single]
  simp [basisImag, monoVal, powR, s1, nx1, ny1, Mono.mul, pointC, pointS, Gauss.re_neg,
    Gauss.im_neg, Gauss.re_i, Gauss.im_i]
  ext <;> simp <;> grind

theorem point_image_a0 :
    evalAt pointC pointS 1 0 0 (applyMat pointBasis (applyMat evolution ket0)).a0 =
      ⟨-(7 : Rat) / 25, 0⟩ := by
  rw [eval_apply_a0, eval_evol_ket0_a0, eval_evol_ket0_a1, pointBasis, eval_const, eval_const]
  exact basis_square_0

theorem point_image_a1 :
    evalAt pointC pointS 1 0 0 (applyMat pointBasis (applyMat evolution ket0)).a1 =
      ⟨0, -(24 : Rat) / 25⟩ := by
  rw [eval_apply_a1, eval_evol_ket0_a0, eval_evol_ket0_a1, pointBasis, eval_const, eval_const]
  exact basis_square_1

/-- Nel punto, `V(U|0⟩)` e `(V U V†)(V|0⟩)` valgono `−7/25` e `−24/25 i`. -/
theorem point_conj_evolution :
    evalAt pointC pointS 1 0 0 (applyMat pointBasis (applyMat evolution ket0)).a0 =
      ⟨-(7 : Rat) / 25, 0⟩ ∧
      evalAt pointC pointS 1 0 0 (applyMat pointBasis (applyMat evolution ket0)).a1 =
        ⟨0, -(24 : Rat) / 25⟩ ∧
      evalAt pointC pointS 1 0 0
          (applyMat (matMul (matMul pointBasis evolution) (matDagger pointBasis))
            (applyMat pointBasis ket0)).a0 =
        ⟨-(7 : Rat) / 25, 0⟩ ∧
      evalAt pointC pointS 1 0 0
          (applyMat (matMul (matMul pointBasis evolution) (matDagger pointBasis))
            (applyMat pointBasis ket0)).a1 =
        ⟨0, -(24 : Rat) / 25⟩ := by
  refine ⟨point_image_a0, point_image_a1, ?_, ?_⟩
  · have h := (conj_evolution pointBasis evolution ket0 point_basis_unitary).1
    rw [← point_image_a0]
    exact (eval_polySame h pointC pointS 1 0 0).symm
  · have h := (conj_evolution pointBasis evolution ket0 point_basis_unitary).2
    rw [← point_image_a1]
    exact (eval_polySame h pointC pointS 1 0 0).symm

/-- Nel punto i pesi di `V|0⟩` nella base `V|k⟩` sono `1` e `0`. -/
theorem point_conj_born :
    evalAt pointC pointS 1 0 0
        (columnBorn (braket (matColumn pointBasis 0) (applyMat pointBasis ket0))) = 1 ∧
      evalAt pointC pointS 1 0 0
          (columnBorn (braket (matColumn pointBasis 1) (applyMat pointBasis ket0))) = 0 := by
  obtain ⟨h0, h1⟩ := conj_born pointBasis ket0 point_basis_unitary
  refine ⟨?_, ?_⟩
  · rw [eval_polySame h0, show ket0.a0 = single (1 : Gauss) Mono.one from rfl, eval_column_const]
    rw [show Gauss.conj (1 : Gauss) = 1 by ext <;> rfl, Gauss.mul_one]
  · rw [eval_polySame h1, show ket0.a1 = [] from rfl, columnBorn_nil]
    rfl

end Universe.Symmetry
