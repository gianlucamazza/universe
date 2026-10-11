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

`U(c₁, s₁) U(c₂, s₂)` e `U(c₁c₂ − s₁s₂, s₁c₂ + c₁s₂)` differiscono per
un cofattore di `gN`: `H² = I` è l'unica regola, il cerchio non entra.
Se le due coppie stanno sul cerchio, ci sta anche il composto, nell'ideale
`(gC, gC2)`. `gC2 = c2² + s2² − 1` resta fuori da `reduce`, come `gA`.
Se `V†V − I` sta in `(gC, gN)`, `V (U ψ)` e `(V U V†) (V ψ)` differiscono
per un elemento di quell'ideale, e così i pesi di Born. Con `V = U` sono
`conj_evolution_law` e `conj_born_law`. `point_compose` legge l'angolo
composto con `evalAt2`.
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

/-- `A (B ψ)` e `ψ` differiscono per `(gC, gN)` quando `AB − I` ci sta. -/
theorem apply_cancel_rel (A B : Mat) (ψ : Pair) (h : matRel (matMul A B) matOne) :
    pairRel (applyMat A (applyMat B ψ)) ψ := by
  have hstep : pairSame (applyMat A (applyMat B ψ)) (applyMat (matMul A B) ψ) :=
    pairSame_symm (apply_assoc A B ψ.a0 ψ.a1)
  have hunit : pairRel (applyMat (matMul A B) ψ) (applyMat matOne ψ) := apply_matRel h ψ
  have hone : pairSame (applyMat matOne ψ) ψ := by
    rw [applyMat_one]
    exact pairSame_refl ψ
  exact pairRel_polySame hstep.symm hone hunit

/-- `V (U ψ)` e `(V U V†) (V ψ)` differiscono per un elemento di `(gC, gN)`
quando `V† V − I` ci sta. -/
theorem conj_evolution_rel (V U : Mat) (ψ : Pair)
    (h : matRel (matMul (matDagger V) V) matOne) :
    pairRel (applyMat V (applyMat U ψ))
      (applyMat (matMul (matMul V U) (matDagger V)) (applyMat V ψ)) := by
  have hback := apply_cancel_rel (matDagger V) V ψ h
  have hmid := apply_pairRel (matMul V U) hback
  have houter := apply_assoc (matMul V U) (matDagger V) (applyMat V ψ).a0 (applyMat V ψ).a1
  have hinner := apply_assoc V U ψ.a0 ψ.a1
  have hright :=
    pairRel_polySame (pairSame.symm houter) (pairSame_refl (applyMat (matMul V U) ψ)) hmid
  exact pairRel_symm (pairRel_trans hright (pairRel_of_pairSame hinner))

/-- `|ξ⟩⟨ξ|`. -/
def outer (ξ : Pair) : Mat where
  a00 := pmul ξ.a0 (conjP ξ.a0)
  a01 := pmul ξ.a0 (conjP ξ.a1)
  a10 := pmul ξ.a1 (conjP ξ.a0)
  a11 := pmul ξ.a1 (conjP ξ.a1)

theorem outer_row (left bra0 bra1 ket0 ket1 : Poly) :
    polySame (pmul (pmul left bra0) ket0 ++ pmul (pmul left bra1) ket1)
      (pmul left (pmul bra0 ket0 ++ pmul bra1 ket1)) := by
  intro t
  rw [pmul_assoc, pmul_assoc]
  exact (polySame.symm (polySame_mul_append_right left _ _)) t

theorem outer_apply (ξ φ : Pair) :
    polySame (applyMat (outer ξ) φ).a0 (pmul ξ.a0 (braket ξ φ)) ∧
      polySame (applyMat (outer ξ) φ).a1 (pmul ξ.a1 (braket ξ φ)) := by
  refine ⟨?_, ?_⟩
  · rw [applyMat, outer, braket]
    exact outer_row ξ.a0 (conjP ξ.a0) (conjP ξ.a1) φ.a0 φ.a1
  · rw [applyMat, outer, braket]
    exact outer_row ξ.a1 (conjP ξ.a0) (conjP ξ.a1) φ.a0 φ.a1

/-- `conj(⟨ξ|φ⟩) = ⟨φ|ξ⟩`. -/
theorem conj_braket (ξ φ : Pair) : polySame (conjP (braket ξ φ)) (braket φ ξ) := by
  intro t
  rw [show conjP (braket ξ φ) =
      conjP (pmul (conjP ξ.a0) φ.a0 ++ pmul (conjP ξ.a1) φ.a1) from rfl,
    conj_append, conj_pmul, conj_pmul, conjP_conjP, conjP_conjP,
    show braket φ ξ = pmul (conjP φ.a0) ξ.a0 ++ pmul (conjP φ.a1) ξ.a1 from rfl]
  exact polySame_append (polySame_mul_comm ξ.a0 (conjP φ.a0))
    (polySame_mul_comm ξ.a1 (conjP φ.a1)) t

/-- `⟨φ|( |ξ⟩⟨ξ| )|φ⟩ = ⟨φ|ξ⟩ ⟨ξ|φ⟩`. -/
theorem sandwich_outer (ξ φ : Pair) :
    polySame (sandwich (outer ξ) φ.a0 φ.a1) (pmul (braket φ ξ) (braket ξ φ)) := by
  have hrows := outer_apply ξ φ
  rw [sandwich_components (outer ξ) φ.a0 φ.a1]
  refine polySame.trans
      (polySame_append
        (polySame_pmul_right (by simpa [applyMat_proj] using hrows.1) (conjP φ.a0))
        (polySame_pmul_right (by simpa [applyMat_proj] using hrows.2) (conjP φ.a1))) ?_
  intro t
  rw [← pmul_assoc, ← pmul_assoc, ← pmul_append_left]
  rfl

/-- `|⟨ξ|φ⟩|² = ⟨φ|( |ξ⟩⟨ξ| )|φ⟩`. -/
theorem born_as_sandwich (ξ φ : Pair) :
    polySame (columnBorn (braket ξ φ)) (sandwich (outer ξ) φ.a0 φ.a1) :=
  polySame.trans
    (polySame.trans (by rw [columnBorn]; exact polySame_pmul_right (conj_braket ξ φ) (braket ξ φ))
      (polySame_mul_comm (braket ξ φ) (braket φ ξ)))
    (polySame.symm (sandwich_outer ξ φ))

theorem mul_pi0 (V : Mat) : matMul V pi0 = ⟨V.a00, [], V.a10, []⟩ := by
  apply Mat.ext
  · rw [show (matMul V pi0).a00 = pmul V.a00 (single 1 Mono.one) ++ pmul V.a01 [] from rfl,
      pmul_one, pmul_nil, List.append_nil]
  · rw [show (matMul V pi0).a01 = pmul V.a00 [] ++ pmul V.a01 [] from rfl, pmul_nil, pmul_nil,
      List.nil_append]
  · rw [show (matMul V pi0).a10 = pmul V.a10 (single 1 Mono.one) ++ pmul V.a11 [] from rfl,
      pmul_one, pmul_nil, List.append_nil]
  · rw [show (matMul V pi0).a11 = pmul V.a10 [] ++ pmul V.a11 [] from rfl, pmul_nil, pmul_nil,
      List.nil_append]

/-- La colonna `0` di `V`, come `|v₀⟩⟨v₀|`, è `V Π₀ V†`. -/
theorem col0_as_conj (V : Mat) :
    outer (matColumn V 0) = matMul (matMul V pi0) (matDagger V) := by
  rw [mul_pi0]
  apply Mat.ext
  · rw [show (outer (matColumn V 0)).a00 = pmul V.a00 (conjP V.a00) from rfl,
      show (matMul ⟨V.a00, [], V.a10, []⟩ (matDagger V)).a00 =
        pmul V.a00 (conjP V.a00) ++ pmul [] (conjP V.a01) from rfl,
      pmul_nil_left, List.append_nil]
  · rw [show (outer (matColumn V 0)).a01 = pmul V.a00 (conjP V.a10) from rfl,
      show (matMul ⟨V.a00, [], V.a10, []⟩ (matDagger V)).a01 =
        pmul V.a00 (conjP V.a10) ++ pmul [] (conjP V.a11) from rfl,
      pmul_nil_left, List.append_nil]
  · rw [show (outer (matColumn V 0)).a10 = pmul V.a10 (conjP V.a00) from rfl,
      show (matMul ⟨V.a00, [], V.a10, []⟩ (matDagger V)).a10 =
        pmul V.a10 (conjP V.a00) ++ pmul [] (conjP V.a01) from rfl,
      pmul_nil_left, List.append_nil]
  · rw [show (outer (matColumn V 0)).a11 = pmul V.a10 (conjP V.a10) from rfl,
      show (matMul ⟨V.a00, [], V.a10, []⟩ (matDagger V)).a11 =
        pmul V.a10 (conjP V.a10) ++ pmul [] (conjP V.a11) from rfl,
      pmul_nil_left, List.append_nil]

theorem mul_pi1 (V : Mat) : matMul V pi1 = ⟨[], V.a01, [], V.a11⟩ := by
  apply Mat.ext
  · rw [show (matMul V pi1).a00 = pmul V.a00 [] ++ pmul V.a01 [] from rfl, pmul_nil, pmul_nil,
      List.nil_append]
  · rw [show (matMul V pi1).a01 =
        pmul V.a00 [] ++ pmul V.a01 (single 1 Mono.one) from rfl, pmul_nil, pmul_one,
      List.nil_append]
  · rw [show (matMul V pi1).a10 = pmul V.a10 [] ++ pmul V.a11 [] from rfl, pmul_nil, pmul_nil,
      List.nil_append]
  · rw [show (matMul V pi1).a11 =
        pmul V.a10 [] ++ pmul V.a11 (single 1 Mono.one) from rfl, pmul_nil, pmul_one,
      List.nil_append]

/-- La colonna `1` di `V`, come `|v₁⟩⟨v₁|`, è `V Π₁ V†`. -/
theorem col1_as_conj (V : Mat) :
    outer (matColumn V 1) = matMul (matMul V pi1) (matDagger V) := by
  rw [mul_pi1]
  apply Mat.ext
  · rw [show (outer (matColumn V 1)).a00 = pmul V.a01 (conjP V.a01) from rfl,
      show (matMul ⟨[], V.a01, [], V.a11⟩ (matDagger V)).a00 =
        pmul [] (conjP V.a00) ++ pmul V.a01 (conjP V.a01) from rfl,
      pmul_nil_left, List.nil_append]
  · rw [show (outer (matColumn V 1)).a01 = pmul V.a01 (conjP V.a11) from rfl,
      show (matMul ⟨[], V.a01, [], V.a11⟩ (matDagger V)).a01 =
        pmul [] (conjP V.a10) ++ pmul V.a01 (conjP V.a11) from rfl,
      pmul_nil_left, List.nil_append]
  · rw [show (outer (matColumn V 1)).a10 = pmul V.a11 (conjP V.a01) from rfl,
      show (matMul ⟨[], V.a01, [], V.a11⟩ (matDagger V)).a10 =
        pmul [] (conjP V.a00) ++ pmul V.a11 (conjP V.a01) from rfl,
      pmul_nil_left, List.nil_append]
  · rw [show (outer (matColumn V 1)).a11 = pmul V.a11 (conjP V.a11) from rfl,
      show (matMul ⟨[], V.a01, [], V.a11⟩ (matDagger V)).a11 =
        pmul [] (conjP V.a10) ++ pmul V.a11 (conjP V.a11) from rfl,
      pmul_nil_left, List.nil_append]

/-- `V† (V P V†) V` e `P` differiscono per `(gC, gN)` quando `V† V − I` ci sta. -/
theorem proj_pull (V P K : Mat) (h : matRel (matMul (matDagger V) V) matOne)
    (houter : K = matMul (matMul V P) (matDagger V)) :
    matRel (matMul (matDagger V) (matMul K V)) P := by
  rw [houter]
  have hassoc := matRel_of_matSame (pull_assoc (matDagger V) V P)
  have hL := matMul_left_rel (matMul_left_rel h P) (matMul (matDagger V) V)
  have hR := matMul_right_rel (matMul matOne P) h
  have hI : matMul (matMul matOne P) matOne = P := by
    rw [matMul_one_right, matMul_one_left]
  have hstep := matRel_trans hassoc (matRel_trans hL hR)
  rw [hI] at hstep
  exact hstep

/-- I pesi di Born di `Vψ` nella base `V|k⟩` e quelli di `ψ` differiscono
per un elemento di `(gC, gN)`, quando `V† V − I` ci sta. -/
theorem conj_born_rel (V : Mat) (ψ : Pair)
    (h : matRel (matMul (matDagger V) V) matOne) :
    inIdeal (psub (columnBorn (braket (matColumn V 0) (applyMat V ψ))) (columnBorn ψ.a0)) ∧
      inIdeal (psub (columnBorn (braket (matColumn V 1) (applyMat V ψ))) (columnBorn ψ.a1)) := by
  refine ⟨?_, ?_⟩
  · have hmat := proj_pull V pi0 (outer (matColumn V 0)) h (col0_as_conj V)
    have hsand := sandwich_rel hmat ψ.a0 ψ.a1
    have hleft :=
      polySame.trans (born_as_sandwich (matColumn V 0) (applyMat V ψ))
        (sandwich_conj (outer (matColumn V 0)) V ψ.a0 ψ.a1)
    exact inIdeal_polySame (polySame_psub hleft (projector_born ψ.a0 ψ.a1).symm) hsand
  · have hmat := proj_pull V pi1 (outer (matColumn V 1)) h (col1_as_conj V)
    have hsand := sandwich_rel hmat ψ.a0 ψ.a1
    have hleft :=
      polySame.trans (born_as_sandwich (matColumn V 1) (applyMat V ψ))
        (sandwich_conj (outer (matColumn V 1)) V ψ.a0 ψ.a1)
    exact inIdeal_polySame (polySame_psub hleft (projector_born_1 ψ.a0 ψ.a1).symm) hsand

/-- La legge simbolica: `V = U`, unitaria solo modulo `δ`. -/
theorem conj_evolution_law (U : Mat) (ψ : Pair) :
    pairRel (applyMat evolution (applyMat U ψ))
      (applyMat (matMul (matMul evolution U) (matDagger evolution)) (applyMat evolution ψ)) :=
  conj_evolution_rel evolution U ψ evolution_unitary

/-- I pesi di Born della legge, con `V = U`. -/
theorem conj_born_law (ψ : Pair) :
    inIdeal
        (psub (columnBorn (braket (matColumn evolution 0) (applyMat evolution ψ)))
          (columnBorn ψ.a0)) ∧
      inIdeal
        (psub (columnBorn (braket (matColumn evolution 1) (applyMat evolution ψ)))
          (columnBorn ψ.a1)) :=
  conj_born_rel evolution ψ evolution_unitary

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

/-! ### Composizione nel tempo -/

def c2One : Mono := {Mono.one with c2 := 1}

def s2One : Mono := {Mono.one with s2 := 1}

def c2Sq : Mono := {Mono.one with c2 := 2}

def s2Sq : Mono := {Mono.one with s2 := 2}

def c2P : Poly := single 1 c2One

def s2P : Poly := single 1 s2One

/-- `−i s₂`. -/
def gamma2 : Poly := single (-Gauss.i) s2One

/-- `c₂² + s₂² − 1`. Generatore fuori da `reduce`, come `gA`. -/
def gC2 : Poly := single 1 c2Sq ++ single 1 s2Sq ++ single (-1) Mono.one

/-- `c₁ c₂ − s₁ s₂`. -/
def angleC : Poly := psub (pmul cP c2P) (pmul (single 1 s1) s2P)

/-- `s₁ c₂ + c₁ s₂`. -/
def angleS : Poly := pmul (single 1 s1) c2P ++ pmul cP s2P

/-- `U(c₂, s₂) = c₂ I − i s₂ H`. -/
def evolution2 : Mat := lin c2P gamma2 hamiltonian

/-- `U(c₁c₂ − s₁s₂, s₁c₂ + c₁s₂)`. -/
def evolutionAdd : Mat :=
  lin angleC (pmul (single (-Gauss.i) Mono.one) angleS) hamiltonian

/-- Appartenenza all'ideale di `gN`, con un solo cofattore. Il cerchio non entra. -/
def inIdealN (p : Poly) : Prop :=
  ∃ f, polySame p (pmul f gN)

def matRelN (M N : Mat) : Prop :=
  inIdealN (psub M.a00 N.a00) ∧ inIdealN (psub M.a01 N.a01) ∧
    inIdealN (psub M.a10 N.a10) ∧ inIdealN (psub M.a11 N.a11)

/-- Appartenenza a `(gC, gC2)`, con due cofattori. `gC2` non entra in `reduce`. -/
def inIdealCircle (p : Poly) : Prop :=
  ∃ f1 f2, polySame p (pmul f1 gC ++ pmul f2 gC2)

theorem inIdealN_zero : inIdealN [] := by
  refine ⟨[], ?_⟩
  rw [show pmul ([] : Poly) gN = [] from pmul_nil_left _]
  exact polySame_refl _

theorem inIdealN_polySame {p q : Poly} (h : polySame p q) (hq : inIdealN q) : inIdealN p := by
  rcases hq with ⟨f, hq⟩
  exact ⟨f, polySame.trans h hq⟩

theorem inIdealN_mul {p : Poly} (k : Poly) (hp : inIdealN p) : inIdealN (pmul k p) := by
  rcases hp with ⟨f, hp⟩
  refine ⟨pmul k f, ?_⟩
  intro t
  rw [(polySame_pmul_right hp k) t, pmul_assoc]

theorem lin_polySame {p p' q q' : Poly} (hp : polySame p p') (hq : polySame q q') (H : Mat) :
    matSame (lin p q H) (lin p' q' H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    rw [lin_a00, lin_a00, coeffOf_append, coeffOf_append, hp t, polySame_pmul_left hq H.a00 t]
  · intro t
    rw [show (lin p q H).a01 = pmul q H.a01 from rfl,
      show (lin p' q' H).a01 = pmul q' H.a01 from rfl, polySame_pmul_left hq H.a01 t]
  · intro t
    rw [show (lin p q H).a10 = pmul q H.a10 from rfl,
      show (lin p' q' H).a10 = pmul q' H.a10 from rfl, polySame_pmul_left hq H.a10 t]
  · intro t
    rw [lin_a11, lin_a11, coeffOf_append, coeffOf_append, hp t, polySame_pmul_left hq H.a11 t]

/-- L'entrata diagonale di `(p I + q H)(r I + u H)`, in forma sparsa. -/
theorem lin_diag_expand (p q r u a b c d : Poly) :
    polySame
      (pmul (p ++ pmul q a) (r ++ pmul u c) ++ pmul (pmul q b) (pmul u d))
      (pmul p r ++ pmul (pmul p u) c ++ pmul (pmul q r) a ++
        pmul (pmul q u) (pmul a c) ++ pmul (pmul q u) (pmul b d)) := by
  intro t
  rw [pmul_append_left, coeffOf_append, coeffOf_append]
  rw [(polySame_mul_append_right p r (pmul u c)) t]
  rw [(polySame_mul_append_right (pmul q a) r (pmul u c)) t]
  rw [coeffOf_append, coeffOf_append]
  rw [← pmul_assoc p u c]
  rw [(polySame_slide_mid q a r) t]
  rw [(polySame_middle_comm q a u c) t]
  rw [(polySame_middle_comm q b u d) t]
  rw [coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append]
  exact Gauss.add_assoc5_flat _ _ _ _ _

/-- L'entrata fuori diagonale, in forma sparsa. -/
theorem lin_off_expand (p q r u a b c d : Poly) :
    polySame
      (pmul (p ++ pmul q a) (pmul u b) ++ pmul (pmul q c) (r ++ pmul u d))
      (pmul (pmul p u) b ++ pmul (pmul q r) c ++
        pmul (pmul q u) (pmul a b) ++ pmul (pmul q u) (pmul c d)) := by
  intro t
  rw [pmul_append_left, coeffOf_append]
  rw [(polySame_mul_append_right (pmul q c) r (pmul u d)) t]
  rw [coeffOf_append, coeffOf_append]
  rw [← pmul_assoc p u b]
  rw [(polySame_middle_comm q a u b) t]
  rw [(polySame_slide_mid q c r) t]
  rw [(polySame_middle_comm q c u d) t]
  rw [coeffOf_append, coeffOf_append, coeffOf_append]
  exact Gauss.add_swap_mid_flat _ _ _ _

/-- `(p I + q H)(r I + u H) − ((pr + qu) I + (pu + qr) H)` è `qu · (H² − I)`. -/
theorem lin_mul (p q r u : Poly) (H : Mat) :
    matSame (matMul (lin p q H) (lin r u H))
      (matAdd
        (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H)
        (matScale (pmul q u) (matAdd (matMul H H) (matNeg matOne)))) := by
  have hneg : pneg (single (1 : Gauss) Mono.one) = single (-1) Mono.one := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    have hL : coeffOf (matMul (lin p q H) (lin r u H)).a00 t =
        coeffOf
          (pmul p r ++ pmul (pmul p u) H.a00 ++ pmul (pmul q r) H.a00 ++
            pmul (pmul q u) (pmul H.a00 H.a00) ++ pmul (pmul q u) (pmul H.a01 H.a10)) t := by
      rw [show (matMul (lin p q H) (lin r u H)).a00 =
          pmul (lin p q H).a00 (lin r u H).a00 ++ pmul (lin p q H).a01 (lin r u H).a10 from rfl]
      rw [lin_a00, show (lin p q H).a01 = pmul q H.a01 from rfl, lin_a00,
        show (lin r u H).a10 = pmul u H.a10 from rfl]
      exact lin_diag_expand p q r u H.a00 H.a01 H.a00 H.a10 t
    have hR : coeffOf
        (matAdd
          (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H)
          (matScale (pmul q u) (matAdd (matMul H H) (matNeg matOne)))).a00 t =
        ((coeffOf (pmul p r) t + coeffOf (pmul q u) t) +
          (coeffOf (pmul (pmul p u) H.a00) t + coeffOf (pmul (pmul q r) H.a00) t)) +
        ((coeffOf (pmul (pmul q u) (pmul H.a00 H.a00)) t +
          coeffOf (pmul (pmul q u) (pmul H.a01 H.a10)) t) +
          -coeffOf (pmul q u) t) := by
      unfold matAdd matScale matNeg matMul matOne
      rw [lin_a00, pmul_append_left, hneg]
      rw [coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append]
      rw [(polySame_mul_append_right (pmul q u)
        (pmul H.a00 H.a00 ++ pmul H.a01 H.a10) (single (-1) Mono.one)) t]
      rw [coeffOf_append]
      rw [(polySame_mul_append_right (pmul q u) (pmul H.a00 H.a00) (pmul H.a01 H.a10)) t]
      rw [coeffOf_append]
      rw [show pmul (pmul q u) (single (-1) Mono.one) = pneg (pmul q u) by
        rw [pmul_right_unit, scale_neg_one]]
      rw [coeff_pneg]
    rw [hL, hR, coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append]
    exact (Gauss.cancel_to_flat _ _ _ _ _ _).symm
  · intro t
    have hL : coeffOf (matMul (lin p q H) (lin r u H)).a01 t =
        coeffOf
          (pmul (pmul p u) H.a01 ++ pmul (pmul q r) H.a01 ++
            pmul (pmul q u) (pmul H.a00 H.a01) ++ pmul (pmul q u) (pmul H.a01 H.a11)) t := by
      rw [show (matMul (lin p q H) (lin r u H)).a01 =
          pmul (lin p q H).a00 (lin r u H).a01 ++ pmul (lin p q H).a01 (lin r u H).a11 from rfl]
      rw [lin_a00, show (lin p q H).a01 = pmul q H.a01 from rfl,
        show (lin r u H).a01 = pmul u H.a01 from rfl, lin_a11]
      exact lin_off_expand p q r u H.a00 H.a01 H.a01 H.a11 t
    have hR : coeffOf
        (matAdd
          (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H)
          (matScale (pmul q u) (matAdd (matMul H H) (matNeg matOne)))).a01 t =
        (coeffOf (pmul (pmul p u) H.a01) t + coeffOf (pmul (pmul q r) H.a01) t) +
        (coeffOf (pmul (pmul q u) (pmul H.a00 H.a01)) t +
          coeffOf (pmul (pmul q u) (pmul H.a01 H.a11)) t) := by
      unfold matAdd matScale matNeg matMul matOne
      rw [show (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H).a01 =
          pmul (pmul p u ++ pmul q r) H.a01 from rfl, pmul_append_left]
      rw [show pneg ([] : Poly) = [] from rfl, List.append_nil]
      rw [coeffOf_append, coeffOf_append]
      rw [(polySame_mul_append_right (pmul q u) (pmul H.a00 H.a01) (pmul H.a01 H.a11)) t]
      rw [coeffOf_append]
    rw [hL, hR, coeffOf_append, coeffOf_append, coeffOf_append]
    exact Gauss.add_assoc _ _ _
  · intro t
    have hL : coeffOf (matMul (lin p q H) (lin r u H)).a10 t =
        coeffOf
          (pmul (pmul p u) H.a10 ++ pmul (pmul q r) H.a10 ++
            pmul (pmul q u) (pmul H.a11 H.a10) ++ pmul (pmul q u) (pmul H.a10 H.a00)) t := by
      rw [show (matMul (lin p q H) (lin r u H)).a10 =
          pmul (lin p q H).a10 (lin r u H).a00 ++ pmul (lin p q H).a11 (lin r u H).a10 from rfl]
      rw [(polySame_append_comm _ _) t]
      rw [lin_a11, show (lin r u H).a10 = pmul u H.a10 from rfl,
        show (lin p q H).a10 = pmul q H.a10 from rfl, lin_a00]
      exact lin_off_expand p q r u H.a11 H.a10 H.a10 H.a00 t
    have hR : coeffOf
        (matAdd
          (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H)
          (matScale (pmul q u) (matAdd (matMul H H) (matNeg matOne)))).a10 t =
        (coeffOf (pmul (pmul p u) H.a10) t + coeffOf (pmul (pmul q r) H.a10) t) +
        (coeffOf (pmul (pmul q u) (pmul H.a10 H.a00)) t +
          coeffOf (pmul (pmul q u) (pmul H.a11 H.a10)) t) := by
      rw [show (matAdd
            (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H)
            (matScale (pmul q u) (matAdd (matMul H H) (matNeg matOne)))).a10 =
          (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H).a10 ++
            (matScale (pmul q u) (matAdd (matMul H H) (matNeg matOne))).a10 from rfl]
      rw [show (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H).a10 =
          pmul (pmul p u ++ pmul q r) H.a10 from rfl, pmul_append_left]
      rw [show (matScale (pmul q u) (matAdd (matMul H H) (matNeg matOne))).a10 =
          pmul (pmul q u) (matAdd (matMul H H) (matNeg matOne)).a10 from rfl]
      rw [show (matAdd (matMul H H) (matNeg matOne)).a10 =
          (matMul H H).a10 ++ (matNeg matOne).a10 from rfl]
      rw [show (matMul H H).a10 = pmul H.a10 H.a00 ++ pmul H.a11 H.a10 from rfl]
      rw [show (matNeg matOne).a10 = [] from rfl, List.append_nil]
      rw [coeffOf_append, coeffOf_append]
      rw [(polySame_mul_append_right (pmul q u) (pmul H.a10 H.a00) (pmul H.a11 H.a10)) t]
      rw [coeffOf_append]
    rw [hL, hR, coeffOf_append, coeffOf_append, coeffOf_append]
    exact Gauss.flat_swap_tail _ _ _ _
  · intro t
    have hL : coeffOf (matMul (lin p q H) (lin r u H)).a11 t =
        coeffOf
          (pmul p r ++ pmul (pmul p u) H.a11 ++ pmul (pmul q r) H.a11 ++
            pmul (pmul q u) (pmul H.a11 H.a11) ++ pmul (pmul q u) (pmul H.a10 H.a01)) t := by
      rw [show (matMul (lin p q H) (lin r u H)).a11 =
          pmul (lin p q H).a10 (lin r u H).a01 ++ pmul (lin p q H).a11 (lin r u H).a11 from rfl]
      rw [(polySame_append_comm _ _) t]
      rw [show (lin p q H).a10 = pmul q H.a10 from rfl,
        show (lin r u H).a01 = pmul u H.a01 from rfl, lin_a11, lin_a11]
      exact lin_diag_expand p q r u H.a11 H.a10 H.a11 H.a01 t
    have hR : coeffOf
        (matAdd
          (lin (pmul p r ++ pmul q u) (pmul p u ++ pmul q r) H)
          (matScale (pmul q u) (matAdd (matMul H H) (matNeg matOne)))).a11 t =
        ((coeffOf (pmul p r) t + coeffOf (pmul q u) t) +
          (coeffOf (pmul (pmul p u) H.a11) t + coeffOf (pmul (pmul q r) H.a11) t)) +
        ((coeffOf (pmul (pmul q u) (pmul H.a10 H.a01)) t +
          coeffOf (pmul (pmul q u) (pmul H.a11 H.a11)) t) +
          -coeffOf (pmul q u) t) := by
      unfold matAdd matScale matNeg matMul matOne
      rw [lin_a11, pmul_append_left, hneg]
      rw [coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append]
      rw [(polySame_mul_append_right (pmul q u)
        (pmul H.a10 H.a01 ++ pmul H.a11 H.a11) (single (-1) Mono.one)) t]
      rw [coeffOf_append]
      rw [(polySame_mul_append_right (pmul q u) (pmul H.a10 H.a01) (pmul H.a11 H.a11)) t]
      rw [coeffOf_append]
      rw [show pmul (pmul q u) (single (-1) Mono.one) = pneg (pmul q u) by
        rw [pmul_right_unit, scale_neg_one]]
      rw [coeff_pneg]
    rw [hL, hR, coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append]
    exact (Gauss.cancel_to_flat_swap _ _ _ _ _ _).symm


theorem angleC_factors : angleC = pmul cP c2P ++ pmul gamma gamma2 := by
  rw [angleC, cP, c2P, s2P, gamma, gamma2]
  rw [pmul_single_single, pmul_single_single, pmul_single_single]
  simp only [Gauss.mul_one, minus_i_sq, psub, List.append_nil]
  rfl

theorem angleS_factor :
    polySame (pmul (single (-Gauss.i) Mono.one) angleS) (pmul cP gamma2 ++ pmul gamma c2P) := by
  rw [angleS, cP, c2P, s2P, gamma, gamma2]
  intro t
  rw [(polySame_mul_append_right (single (-Gauss.i) Mono.one)
        (pmul (single (1 : Gauss) s1) (single (1 : Gauss) c2One))
        (pmul (single (1 : Gauss) c1) (single (1 : Gauss) s2One))) t]
  rw [← pmul_assoc (single (-Gauss.i) Mono.one) (single (1 : Gauss) s1) (single (1 : Gauss) c2One)]
  rw [← pmul_assoc (single (-Gauss.i) Mono.one) (single (1 : Gauss) c1) (single (1 : Gauss) s2One)]
  rw [pmul_single_single, pmul_single_single, pmul_single_single, pmul_single_single]
  rw [List.append_nil, List.append_nil, List.append_nil, List.append_nil]
  rw [pmul_single_single, pmul_single_single]
  rw [List.append_nil, List.append_nil]
  simp only [Gauss.mul_one, Gauss.one_mul, Mono.one_mul]
  rw [coeffOf_append, coeffOf_append, Gauss.add_comm]

theorem gamma_square : pmul gamma gamma2 = single (-1) (s1.mul s2One) ++ [] := by
  rw [gamma, gamma2, pmul_single_single, minus_i_sq]

theorem gamma_on_gN :
    polySame (pmul (pmul gamma gamma2) gN) (pmul (single (-1) (s1.mul s2One)) gN) := by
  rw [gamma_square]
  intro t
  rw [pmul_append_left, pmul_nil_left, coeffOf_append, coeffOf_nil, Gauss.add_zero]

theorem h2_diag (h : polySame (matMul hamiltonian hamiltonian).a00 axisSq) :
    polySame (psub (matMul hamiltonian hamiltonian).a00 (single 1 Mono.one)) gN := by
  refine polySame.trans (polySame_psub h (polySame_refl _)) ?_
  refine polySame.trans (polySame_psub_one axisSq) ?_
  intro t
  rw [axis_tail]

theorem defect_entry (k row : Poly) (hrow : polySame row []) :
    polySame (pmul k row) [] := by
  intro t
  rw [(polySame_pmul_right hrow k) t, pmul_nil, coeffOf_nil]

theorem evolution_add_same :
    matSame
      (lin (pmul cP c2P ++ pmul gamma gamma2) (pmul cP gamma2 ++ pmul gamma c2P) hamiltonian)
      evolutionAdd := by
  rw [← angleC_factors]
  exact lin_polySame (polySame_refl _) (polySame.symm angleS_factor) hamiltonian

/-- `U(c₁, s₁) U(c₂, s₂) − U(c, s)` sta nell'ideale di `gN`. Il cerchio non serve. -/
theorem evolution_compose : matRelN (matMul evolution evolution2) evolutionAdd := by
  have hmul := lin_mul cP gamma c2P gamma2 hamiltonian
  have hshift := evolution_add_same
  have h00 : polySame (psub (matMul evolution evolution2).a00 evolutionAdd.a00)
      (pmul (pmul gamma gamma2) (psub (matMul hamiltonian hamiltonian).a00 (single 1 Mono.one))) := by
    have hsum : polySame (matMul evolution evolution2).a00
        (evolutionAdd.a00 ++
          pmul (pmul gamma gamma2)
            ((matMul hamiltonian hamiltonian).a00 ++ pneg (single 1 Mono.one))) := by
      refine polySame.trans hmul.1 ?_
      exact polySame_append (hshift.1) (polySame_refl _)
    exact polySame_sub_left hsum
  have h11 : polySame (psub (matMul evolution evolution2).a11 evolutionAdd.a11)
      (pmul (pmul gamma gamma2) (psub (matMul hamiltonian hamiltonian).a11 (single 1 Mono.one))) := by
    have hsum : polySame (matMul evolution evolution2).a11
        (evolutionAdd.a11 ++
          pmul (pmul gamma gamma2)
            ((matMul hamiltonian hamiltonian).a11 ++ pneg (single 1 Mono.one))) := by
      refine polySame.trans hmul.2.2.2 ?_
      exact polySame_append (hshift.2.2.2) (polySame_refl _)
    exact polySame_sub_left hsum
  have h01 : polySame (psub (matMul evolution evolution2).a01 evolutionAdd.a01) [] := by
    have hdef : polySame
        (matScale (pmul gamma gamma2)
          (matAdd (matMul hamiltonian hamiltonian) (matNeg matOne))).a01
        (pmul (pmul gamma gamma2) (matMul hamiltonian hamiltonian).a01) := by
      unfold matScale matAdd matNeg matOne
      rw [show pneg ([] : Poly) = [] from rfl, List.append_nil]
      exact polySame_refl _
    have hsum := polySame.trans hmul.2.1 (polySame_append hshift.2.1 hdef)
    exact polySame.trans (polySame_sub_left hsum) (defect_entry _ _ off_01)
  have h10 : polySame (psub (matMul evolution evolution2).a10 evolutionAdd.a10) [] := by
    have hdef : polySame
        (matScale (pmul gamma gamma2)
          (matAdd (matMul hamiltonian hamiltonian) (matNeg matOne))).a10
        (pmul (pmul gamma gamma2) (matMul hamiltonian hamiltonian).a10) := by
      unfold matScale matAdd matNeg matOne
      rw [show pneg ([] : Poly) = [] from rfl, List.append_nil]
      exact polySame_refl _
    have hsum := polySame.trans hmul.2.2.1 (polySame_append hshift.2.2.1 hdef)
    exact polySame.trans (polySame_sub_left hsum) (defect_entry _ _ off_10)
  refine ⟨?_, inIdealN_polySame h01 inIdealN_zero, inIdealN_polySame h10 inIdealN_zero, ?_⟩
  · refine ⟨single (-1) (s1.mul s2One), ?_⟩
    refine polySame.trans h00 ?_
    refine polySame.trans (polySame_pmul_right (h2_diag diag_00) _) ?_
    exact gamma_on_gN
  · refine ⟨single (-1) (s1.mul s2One), ?_⟩
    refine polySame.trans h11 ?_
    have hdiag : polySame (psub (matMul hamiltonian hamiltonian).a11 (single 1 Mono.one)) gN := by
      refine polySame.trans (polySame_psub diag_11 (polySame_refl _)) ?_
      refine polySame.trans (polySame_psub_one axisSq) ?_
      intro t
      rw [axis_tail]
    refine polySame.trans (polySame_pmul_right hdiag _) ?_
    exact gamma_on_gN

def csSq : Poly := single 1 cSq ++ single 1 sSq

def c2s2Sq : Poly := single 1 c2Sq ++ single 1 s2Sq

theorem neg_one_plus_one : polySame (single (-1) Mono.one ++ single 1 Mono.one) [] := by
  intro t
  rw [coeffOf_append, coeff_single_eq, coeff_single_eq, coeffOf_nil]
  by_cases ht : Mono.one = t
  · rw [ite_eq_left ht, ite_eq_left ht]
    ext <;> simp <;> grind
  · rw [ite_eq_right ht, ite_eq_right ht, Gauss.add_zero]

theorem gC_plus_one : polySame (gC ++ single 1 Mono.one) csSq := by
  rw [gC, csSq]
  refine polySame.trans (polySame_append_assoc _ _ _) ?_
  refine polySame.trans (polySame_append (polySame_refl _) neg_one_plus_one) ?_
  intro t
  rw [coeffOf_append, coeffOf_nil, Gauss.add_zero]

theorem gC2_plus_one : polySame (gC2 ++ single 1 Mono.one) c2s2Sq := by
  rw [gC2, c2s2Sq]
  refine polySame.trans (polySame_append_assoc _ _ _) ?_
  refine polySame.trans (polySame_append (polySame_refl _) neg_one_plus_one) ?_
  intro t
  rw [coeffOf_append, coeffOf_nil, Gauss.add_zero]

/-- `(a + 1)(b + 1) − 1` è `a (b + 1) + b`. -/
theorem succ_mul (a b : Poly) :
    polySame
      (psub (pmul (a ++ single 1 Mono.one) (b ++ single 1 Mono.one)) (single 1 Mono.one))
      (pmul a (b ++ single 1 Mono.one) ++ b) := by
  have hmul : pmul (a ++ single 1 Mono.one) (b ++ single 1 Mono.one) =
      pmul a (b ++ single 1 Mono.one) ++ (b ++ single 1 Mono.one) := by
    rw [pmul_append_left, one_pmul]
  intro t
  rw [coeff_psub, hmul, coeffOf_append, coeffOf_append, coeffOf_append, coeff_single_eq]
  ext <;> simp <;> grind

theorem polySame_bin_mul (a b c d : Gauss) (m n p q : Mono) :
    polySame (pmul (single a m ++ single b n) (single c p ++ single d q))
      (single (a * c) (m.mul p) ++
        (single (a * d) (m.mul q) ++
          (single (b * c) (n.mul p) ++ single (b * d) (n.mul q)))) := by
  intro t
  rw [pmul_append_left, coeffOf_append]
  rw [(polySame_mul_append_right (single a m) (single c p) (single d q)) t]
  rw [(polySame_mul_append_right (single b n) (single c p) (single d q)) t]
  rw [pmul_single_single, pmul_single_single, pmul_single_single, pmul_single_single]
  rw [List.append_nil, List.append_nil, List.append_nil, List.append_nil]
  rw [coeffOf_append, coeffOf_append]
  rw [coeffOf_append4]
  exact Gauss.add_assoc4 _ _ _ _

theorem angleC_bin :
    angleC = single 1 (c1.mul c2One) ++ single (-1) (s1.mul s2One) := by
  rw [angleC, cP, c2P, s2P, pmul_single_single, pmul_single_single]
  simp only [Gauss.mul_one, psub, List.append_nil]
  rfl

theorem angleS_bin :
    angleS = single 1 (s1.mul c2One) ++ single 1 (c1.mul s2One) := by
  rw [angleS, cP, c2P, s2P, pmul_single_single, pmul_single_single]
  simp only [Gauss.mul_one, List.append_nil]

theorem mono_cc : (c1.mul c2One).mul (c1.mul c2One) = cSq.mul c2Sq := by
  ext <;> rfl

theorem mono_ss : (s1.mul s2One).mul (s1.mul s2One) = sSq.mul s2Sq := by
  ext <;> rfl

theorem mono_sc : (s1.mul c2One).mul (s1.mul c2One) = sSq.mul c2Sq := by
  ext <;> rfl

theorem mono_cs : (c1.mul s2One).mul (c1.mul s2One) = cSq.mul s2Sq := by
  ext <;> rfl

theorem mono_cross_left :
    (c1.mul c2One).mul (s1.mul s2One) = (s1.mul s2One).mul (c1.mul c2One) := by
  exact Mono.mul_comm _ _

theorem mono_cross :
    (c1.mul c2One).mul (s1.mul s2One) = (s1.mul c2One).mul (c1.mul s2One) := by
  ext <;> simp [Mono.mul, c1, s1, c2One, s2One, Nat.add_comm]

theorem mono_cross_right :
    (s1.mul c2One).mul (c1.mul s2One) = (c1.mul s2One).mul (s1.mul c2One) := by
  exact Mono.mul_comm _ _

theorem cross_coeff (m t : Mono) :
    coeffOf (single (-1) m) t +
      (coeffOf (single (-1) m) t +
        (coeffOf (single (1 : Gauss) m) t + coeffOf (single (1 : Gauss) m) t)) = 0 := by
  simp only [coeff_single_eq]
  by_cases h : m = t
  · simp only [h]
    ext <;> simp <;> grind
  · simp only [h]
    ext <;> simp <;> grind

/-- I quattro termini di croce sommano a zero; restano i quattro quadrati. -/
theorem angle_terms_same (cross : Mono) :
    polySame
      ((single 1 (cSq.mul c2Sq) ++
          (single (-1) cross ++ (single (-1) cross ++ single 1 (sSq.mul s2Sq)))) ++
        (single 1 (sSq.mul c2Sq) ++
          (single 1 cross ++ (single 1 cross ++ single 1 (cSq.mul s2Sq)))))
      (single 1 (cSq.mul c2Sq) ++
        (single 1 (cSq.mul s2Sq) ++ (single 1 (sSq.mul c2Sq) ++ single 1 (sSq.mul s2Sq)))) := by
  intro t
  rw [coeffOf_append, coeffOf_append4, coeffOf_append4, coeffOf_append4]
  exact Gauss.kill_cross _ _ _ _ _ _ (cross_coeff cross t)

theorem angle_square :
    polySame (pmul angleC angleC ++ pmul angleS angleS) (pmul csSq c2s2Sq) := by
  rw [angleC_bin, angleS_bin]
  refine polySame.trans
    (polySame_append
      (polySame_bin_mul 1 (-1) 1 (-1) (c1.mul c2One) (s1.mul s2One) (c1.mul c2One) (s1.mul s2One))
      (polySame_bin_mul 1 1 1 1 (s1.mul c2One) (c1.mul s2One) (s1.mul c2One) (c1.mul s2One))) ?_
  simp only [Gauss.one_mul, Gauss.mul_one, Gauss.neg_one_mul, Gauss.neg_neg]
  rw [mono_cc, mono_ss, mono_sc, mono_cs, mono_cross, ← mono_cross_left, mono_cross,
    ← mono_cross_right]
  rw [csSq, c2s2Sq]
  refine polySame.trans ?_ (polySame.symm (polySame_bin_mul 1 1 1 1 cSq sSq c2Sq s2Sq))
  simp only [Gauss.mul_one]
  exact angle_terms_same ((s1.mul c2One).mul (c1.mul s2One))

/-- Se le due coppie stanno sul cerchio, ci sta `(c₁c₂ − s₁s₂, s₁c₂ + c₁s₂)`.
I cofattori sono `c₂² + s₂²` e `1`. `reduce` non sbuccia `c2`. -/
theorem compose_circle :
    inIdealCircle (psub (pmul angleC angleC ++ pmul angleS angleS) (single 1 Mono.one)) := by
  refine ⟨c2s2Sq, single 1 Mono.one, ?_⟩
  have hsq : polySame (psub (pmul angleC angleC ++ pmul angleS angleS) (single 1 Mono.one))
      (psub (pmul csSq c2s2Sq) (single 1 Mono.one)) :=
    polySame_psub angle_square (polySame_refl _)
  have hfac : polySame (pmul csSq c2s2Sq) (pmul (gC ++ single 1 Mono.one) (gC2 ++ single 1 Mono.one)) :=
    polySame.trans (polySame_pmul_left (polySame.symm gC_plus_one) c2s2Sq)
      (polySame_pmul_right (polySame.symm gC2_plus_one) (gC ++ single 1 Mono.one))
  have hsucc := succ_mul gC gC2
  have hstep : polySame (psub (pmul csSq c2s2Sq) (single 1 Mono.one))
      (pmul gC (gC2 ++ single 1 Mono.one) ++ gC2) :=
    polySame.trans (polySame_psub hfac (polySame_refl _)) hsucc
  have hunit : polySame gC2 (pmul (single (1 : Gauss) Mono.one) gC2) := by
    intro t
    rw [one_pmul]
  have hcof : polySame (pmul gC (gC2 ++ single 1 Mono.one) ++ gC2)
      (pmul c2s2Sq gC ++ pmul (single 1 Mono.one) gC2) := by
    refine polySame.trans (polySame_append (polySame_pmul_right gC2_plus_one gC) (polySame_refl _)) ?_
    refine polySame.trans (polySame_append (polySame_mul_comm gC c2s2Sq) (polySame_refl _)) ?_
    exact polySame_append (polySame_refl _) hunit
  exact polySame.trans hsq (polySame.trans hstep hcof)

theorem evolution_a01_bin :
    evolution.a01 = single (-Gauss.i) (s1.mul nx1) ++ single (-1) (s1.mul ny1) := by
  have ha : evolution.a01 = pmul gamma h01 := by
    unfold evolution lin
    rfl
  rw [ha, gamma, h01, pmul_two_singles, List.append_nil, Gauss.mul_one, minus_i_sq]

theorem evolution_a11_bin :
    evolution.a11 = single (1 : Gauss) c1 ++ single Gauss.i (s1.mul nz1) := by
  have ha : evolution.a11 = cP ++ pmul gamma h11 := by
    rw [show evolution.a11 = (lin cP gamma hamiltonian).a11 from rfl, lin_a11]
    rfl
  rw [ha, cP, gamma, show h11 = single (-1) nz1 from rfl, pmul_single_single, List.append_nil,
    Gauss.mul_neg_one, Gauss.neg_neg]

theorem evolution2_a00_bin :
    evolution2.a00 = single (1 : Gauss) c2One ++ single (-Gauss.i) (s2One.mul nz1) := by
  unfold evolution2 lin
  rw [pmul_one, gamma2, hamiltonian, h00, pmul_single_single, Gauss.mul_one, List.append_nil, c2P]

theorem evolution2_a10_bin :
    evolution2.a10 =
      single (-Gauss.i) (s2One.mul nx1) ++ single (1 : Gauss) (s2One.mul ny1) := by
  have ha : evolution2.a10 = pmul gamma2 h10 := by
    unfold evolution2 lin hamiltonian
    rfl
  rw [ha, gamma2, h10, pmul_two_singles, List.append_nil, Gauss.mul_one, minus_i_mul_i]

/-- Nel punto, la prima riga di `U` è `3/5` e `−4/5 i`. -/
theorem point_u_row0 :
    evalAt2 pointC pointS 1 0 0 pointC pointS evolution.a00 = basisReal ∧
      evalAt2 pointC pointS 1 0 0 pointC pointS evolution.a01 = basisImag := by
  refine ⟨?_, ?_⟩
  · rw [evolution_a00_bin, evalAt2_append, evalAt2_single, evalAt2_single]
    ext <;> simp [monoImage2, monoVal2, monoVal, powR, c1, s1, nz1, Mono.mul, pointC, pointS,
      basisReal, Gauss.re_neg, Gauss.im_neg, Gauss.re_i, Gauss.im_i] <;> grind
  · rw [evolution_a01_bin, evalAt2_append, evalAt2_single, evalAt2_single]
    ext <;> simp [monoImage2, monoVal2, monoVal, powR, s1, nx1, ny1, Mono.mul, pointC, pointS,
      basisImag, Gauss.re_neg, Gauss.im_neg, Gauss.re_i, Gauss.im_i] <;> grind

/-- Nel punto, la seconda riga di `U` è `−4/5 i` e `3/5`. -/
theorem point_u_row1 :
    evalAt2 pointC pointS 1 0 0 pointC pointS evolution.a10 = basisImag ∧
      evalAt2 pointC pointS 1 0 0 pointC pointS evolution.a11 = basisReal := by
  refine ⟨?_, ?_⟩
  · rw [evolution_a10_bin, evalAt2_append, evalAt2_single, evalAt2_single]
    ext <;> simp [monoImage2, monoVal2, monoVal, powR, s1, nx1, ny1, Mono.mul, pointC, pointS,
      basisImag, Gauss.re_neg, Gauss.im_neg, Gauss.re_i, Gauss.im_i] <;> grind
  · rw [evolution_a11_bin, evalAt2_append, evalAt2_single, evalAt2_single]
    ext <;> simp [monoImage2, monoVal2, monoVal, powR, c1, s1, nz1, Mono.mul, pointC, pointS,
      basisReal, Gauss.re_i, Gauss.im_i] <;> grind

/-- Nel punto, la prima colonna di `U(c₂, s₂)` è `3/5` e `−4/5 i`. -/
theorem point_u2_col0 :
    evalAt2 pointC pointS 1 0 0 pointC pointS evolution2.a00 = basisReal ∧
      evalAt2 pointC pointS 1 0 0 pointC pointS evolution2.a10 = basisImag := by
  refine ⟨?_, ?_⟩
  · rw [evolution2_a00_bin, evalAt2_append, evalAt2_single, evalAt2_single]
    ext <;> simp [monoImage2, monoVal2, monoVal, powR, c2One, s2One, nz1, Mono.mul, pointC, pointS,
      basisReal, Gauss.re_neg, Gauss.im_neg, Gauss.re_i, Gauss.im_i] <;> grind
  · rw [evolution2_a10_bin, evalAt2_append, evalAt2_single, evalAt2_single]
    ext <;> simp [monoImage2, monoVal2, monoVal, powR, s2One, nx1, ny1, Mono.mul, pointC, pointS,
      basisImag, Gauss.re_neg, Gauss.im_neg, Gauss.re_i, Gauss.im_i] <;> grind

theorem basis_square : basisReal * basisReal + basisImag * basisImag = ⟨-(7 : Rat) / 25, 0⟩ := by
  ext <;> simp [basisReal, basisImag, pointC, pointS] <;> grind

theorem basis_cross : basisImag * basisReal + basisReal * basisImag = ⟨0, -(24 : Rat) / 25⟩ := by
  ext <;> simp [basisReal, basisImag, pointC, pointS] <;> grind

/-- Nel punto `c = c₂ = 3/5`, `s = s₂ = 4/5`, `n = e_x`, l'angolo composto è
`(−7/25, 24/25)` e `U U₂ |0⟩ = −7/25 |0⟩ − 24/25 i |1⟩`. -/
theorem point_compose :
    evalAt2 pointC pointS 1 0 0 pointC pointS angleC = ⟨-(7 : Rat) / 25, 0⟩ ∧
      evalAt2 pointC pointS 1 0 0 pointC pointS angleS = ⟨(24 : Rat) / 25, 0⟩ ∧
        evalAt2 pointC pointS 1 0 0 pointC pointS
            (applyMat (matMul evolution evolution2) ket0).a0 = ⟨-(7 : Rat) / 25, 0⟩ ∧
          evalAt2 pointC pointS 1 0 0 pointC pointS
              (applyMat (matMul evolution evolution2) ket0).a1 = ⟨0, -(24 : Rat) / 25⟩ := by
  have hket0 : (applyMat (matMul evolution evolution2) ket0).a0 =
      pmul evolution.a00 evolution2.a00 ++ pmul evolution.a01 evolution2.a10 := by
    rw [applyMat, ket0, matMul, pmul_one, pmul_nil, List.append_nil]
  have hket1 : (applyMat (matMul evolution evolution2) ket0).a1 =
      pmul evolution.a10 evolution2.a00 ++ pmul evolution.a11 evolution2.a10 := by
    simp [applyMat, ket0, matMul, pmul_one, pmul_nil, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [angleC_bin, evalAt2_append, evalAt2_single, evalAt2_single]
    ext <;> simp [monoImage2, monoVal2, monoVal, powR, c1, c2One, s1, s2One, Mono.mul, pointC,
      pointS, Gauss.re_neg, Gauss.im_neg] <;> grind
  · rw [angleS_bin, evalAt2_append, evalAt2_single, evalAt2_single]
    ext <;> simp [monoImage2, monoVal2, monoVal, powR, c1, c2One, s1, s2One, Mono.mul, pointC,
      pointS] <;> grind
  · rw [hket0, evalAt2_append, evalAt2_pmul, evalAt2_pmul, point_u_row0.1, point_u2_col0.1,
      point_u_row0.2, point_u2_col0.2, basis_square]
  · rw [hket1, evalAt2_append, evalAt2_pmul, evalAt2_pmul, point_u_row1.1, point_u2_col0.1,
      point_u_row1.2, point_u2_col0.2, basis_cross]

end Universe.Symmetry
