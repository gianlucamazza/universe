/-
Osservazione.

`Φ|0⟩` è la prima colonna di `U`. `P(0) + P(1) − 1` ha i cofattori di
`gC + s² gN`. Le ampiezze di `|0⟩` sono `1` e `0`.

`|z|² = re² + im²` e la razionalità dei coefficienti sono identità libere.
`projector_born` è `⟨ψ|Π₀|ψ⟩ = |α|²`. `sphere_prob_sum` aggiunge `gA`
sullo stato generico. `literal_sandwich` identifica il modulo letterale
`|γ₀|² + |γ₁|²` con il sandwich, per ogni matrice. `keepX` e `keepZ`
specializzano un asse e, per questi due, `spec` è un omomorfismo d'anello.
`axis_x_born0` e `axis_z_born0` partono dai pesi di Born. `axis_z_gn`
azzera `gN` lungo z. Il punto `c = 3/5`, `s = 4/5`, `n = e_x` valuta
`δ` e i pesi lungo x.
-/
import Universe.Qubit

namespace Universe.Epistemology

open Universe.Ring
open Universe.Quotient hiding mul
open Universe.Dynamics
open Universe.Qubit

/-- Modulo quadro `z · conj(z)`. -/
def columnBorn (z : Poly) : Poly := pmul z (conjP z)

def groundP0 : Poly := columnBorn evolution.a00

def groundP1 : Poly := columnBorn evolution.a10

theorem columnBorn_comm (z : Poly) (t : Mono) :
    coeffOf (columnBorn z) t = coeffOf (pmul (conjP z) z) t := by
  rw [columnBorn, coeff_mul_comm]

/-- La somma dei pesi di Born di `Φ|0⟩` è l'entrata `(U†U)₀₀`. -/
theorem ground_born_sum (t : Mono) :
    coeffOf (groundP0 ++ groundP1) t =
      coeffOf (matMul (matDagger evolution) evolution).a00 t := by
  rw [groundP0, groundP1, columnBorn, columnBorn, matMul, matDagger,
    coeffOf_append, coeffOf_append,
    coeff_mul_comm evolution.a00 (conjP evolution.a00),
    coeff_mul_comm evolution.a10 (conjP evolution.a10)]

theorem ground_prob_defect :
    polySame (psub (groundP0 ++ groundP1) (single 1 Mono.one)) unitaryDefect := by
  intro t
  rw [coeff_psub, ground_born_sum, ← coeff_psub]
  exact evolution_unitary_00 t

/-- `P(0) + P(1) − 1` sullo stato fondamentale evoluto ha i cofattori di δ. -/
theorem ground_prob_sum :
    inIdeal (psub (groundP0 ++ groundP1) (single 1 Mono.one)) :=
  inIdeal_polySame ground_prob_defect unitary_ideal

/-! ### `|z|²` nell'anello libero -/

def reG (z : Gauss) : Gauss := ⟨z.re, 0⟩

def imG (z : Gauss) : Gauss := ⟨z.im, 0⟩

theorem reG_zero : reG 0 = 0 := by
  ext <;> simp [reG]

theorem imG_zero : imG 0 = 0 := by
  ext <;> simp [imG]

theorem reG_add (z w : Gauss) : reG (z + w) = reG z + reG w := by
  ext
  · rfl
  · exact (Rat.zero_add 0).symm

theorem imG_add (z w : Gauss) : imG (z + w) = imG z + imG w := by
  ext
  · rfl
  · exact (Rat.zero_add 0).symm

theorem conj_reG (z : Gauss) : Gauss.conj (reG z) = reG z := by
  ext <;> simp [reG, Gauss.conj]

theorem conj_imG (z : Gauss) : Gauss.conj (imG z) = imG z := by
  ext <;> simp [imG, Gauss.conj]

theorem gauss_sum4 (a b c d : Gauss) : (a + b) + (c + d) = a + ((b + c) + d) := by
  rw [Gauss.add_assoc, Gauss.add_assoc, ← Gauss.add_assoc b c d]

theorem mul_conj_parts (z : Gauss) :
    z * Gauss.conj z = reG z * reG z + imG z * imG z := by
  ext <;> simp [reG, imG, Gauss.conj] <;> grind

theorem polar_cross (z w : Gauss) :
    z * Gauss.conj w + Gauss.conj z * w =
      reG z * reG w + reG z * reG w + (imG z * imG w + imG z * imG w) := by
  ext <;> simp [reG, imG, Gauss.conj] <;> grind

def splitRe : Poly → Poly
  | [] => []
  | (a, m) :: rest => (reG a, m) :: splitRe rest

def splitIm : Poly → Poly
  | [] => []
  | (a, m) :: rest => (imG a, m) :: splitIm rest

def modulusSq (p : Poly) : Poly := pmul p (conjP p)

def partSquares (p : Poly) : Poly :=
  pmul (splitRe p) (splitRe p) ++ pmul (splitIm p) (splitIm p)

theorem coeff_splitRe (p : Poly) (t : Mono) :
    coeffOf (splitRe p) t = reG (coeffOf p t) := by
  induction p with
  | nil =>
    simp only [splitRe, coeffOf]
    exact reG_zero.symm
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [splitRe, coeffOf, coeffOf, ih]
      by_cases h : m = t
      · rw [ite_eq_left h, ite_eq_left h, ← reG_add]
      · rw [ite_eq_right h, ite_eq_right h, reG_add, reG_zero, Gauss.zero_add]

theorem coeff_splitIm (p : Poly) (t : Mono) :
    coeffOf (splitIm p) t = imG (coeffOf p t) := by
  induction p with
  | nil =>
    simp only [splitIm, coeffOf]
    exact imG_zero.symm
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [splitIm, coeffOf, coeffOf, ih]
      by_cases h : m = t
      · rw [ite_eq_left h, ite_eq_left h, ← imG_add]
      · rw [ite_eq_right h, ite_eq_right h, imG_add, imG_zero, Gauss.zero_add]

theorem coeff_cross (a : Gauss) (m : Mono) (q : Poly) (t : Mono) :
    coeffOf (mulMono a m (conjP q) ++ pmul q (single (Gauss.conj a) m)) t =
      coeffOf ((mulMono (reG a) m (splitRe q) ++ pmul (splitRe q) (single (reG a) m)) ++
        (mulMono (imG a) m (splitIm q) ++ pmul (splitIm q) (single (imG a) m))) t := by
  have hL :
      coeffOf (mulMono a m (conjP q) ++ pmul q (single (Gauss.conj a) m)) t =
        coeffOf (mulMono a m (conjP q)) t + coeffOf (mulMono (Gauss.conj a) m q) t := by
    rw [coeffOf_append, coeff_single_right]
  have hRe :
      coeffOf (mulMono (reG a) m (splitRe q) ++ pmul (splitRe q) (single (reG a) m)) t =
        coeffOf (mulMono (reG a) m (splitRe q)) t +
          coeffOf (mulMono (reG a) m (splitRe q)) t := by
    rw [coeffOf_append, coeff_single_right]
  have hIm :
      coeffOf (mulMono (imG a) m (splitIm q) ++ pmul (splitIm q) (single (imG a) m)) t =
        coeffOf (mulMono (imG a) m (splitIm q)) t +
          coeffOf (mulMono (imG a) m (splitIm q)) t := by
    rw [coeffOf_append, coeff_single_right]
  rw [hL, coeffOf_append, hRe, hIm, coeffOf_mulMono, coeffOf_mulMono, coeffOf_mulMono,
    coeffOf_mulMono]
  cases hsub : subExp t m with
  | none =>
    simp [factor, hsub, Gauss.zero_add]
  | some k =>
    simp only [factor, hsub, coeff_conj, coeff_splitRe, coeff_splitIm]
    exact polar_cross a (coeffOf q k)

theorem coeff_modulus_cons (a : Gauss) (m : Mono) (q : Poly) (t : Mono) :
    coeffOf (modulusSq ((a, m) :: q)) t =
      (if m.mul m = t then a * Gauss.conj a else 0) +
        (coeffOf (mulMono a m (conjP q) ++ pmul q (single (Gauss.conj a) m)) t +
          coeffOf (modulusSq q) t) := by
  rw [modulusSq, show conjP ((a, m) :: q) = single (Gauss.conj a) m ++ conjP q from rfl,
    show pmul ((a, m) :: q) (single (Gauss.conj a) m ++ conjP q) =
      mulMono a m (single (Gauss.conj a) m ++ conjP q) ++
        pmul q (single (Gauss.conj a) m ++ conjP q) from rfl,
    mulMono_append, coeffOf_append, coeff_mul_append_right,
    show mulMono a m (single (Gauss.conj a) m) = single (a * Gauss.conj a) (m.mul m) from by
      simp [mulMono, single]]
  rw [coeffOf_append, coeffOf_append, coeff_single_eq, modulusSq]
  rw [coeffOf_append (mulMono a m (conjP q)) (pmul q (single (Gauss.conj a) m))]
  exact gauss_sum4 _ _ _ _

theorem conj_splitRe (p : Poly) : conjP (splitRe p) = splitRe p := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [splitRe, conjP, ih, conj_reG]

theorem conj_splitIm (p : Poly) : conjP (splitIm p) = splitIm p := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [splitIm, conjP, ih, conj_imG]

theorem partSquares_modulus (p : Poly) (t : Mono) :
    coeffOf (partSquares p) t =
      coeffOf (modulusSq (splitRe p)) t + coeffOf (modulusSq (splitIm p)) t := by
  have hre : pmul (splitRe p) (splitRe p) = modulusSq (splitRe p) := by
    rw [modulusSq, conj_splitRe]
  have him : pmul (splitIm p) (splitIm p) = modulusSq (splitIm p) := by
    rw [modulusSq, conj_splitIm]
  rw [partSquares, coeffOf_append, hre, him]

theorem diag_parts (a : Gauss) (cond : Prop) [Decidable cond] :
    (if cond then a * Gauss.conj a else 0) =
      (if cond then reG a * Gauss.conj (reG a) else 0) +
        (if cond then imG a * Gauss.conj (imG a) else 0) := by
  by_cases h : cond
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, conj_reG, conj_imG, mul_conj_parts]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, Gauss.zero_add]

theorem arrange_modulus (d dr di c cr ci q qr qi : Gauss)
    (hd : d = dr + di) (hc : c = cr + ci) (hq : q = qr + qi) :
    d + (c + q) = (dr + (cr + qr)) + (di + (ci + qi)) := by
  rw [hd, hc, hq]
  ext <;> simp <;> grind

/-- `z · conj(z)` e `re(z)² + im(z)²` hanno gli stessi coefficienti. -/
theorem modulus_squares (p : Poly) (t : Mono) :
    coeffOf (modulusSq p) t = coeffOf (partSquares p) t := by
  induction p with
  | nil =>
    simp [modulusSq, partSquares, splitRe, splitIm, pmul, Universe.Quotient.mul, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [partSquares_modulus, coeff_modulus_cons a m rest,
        show splitRe ((a, m) :: rest) = (reG a, m) :: splitRe rest from rfl,
        show splitIm ((a, m) :: rest) = (imG a, m) :: splitIm rest from rfl,
        coeff_modulus_cons (reG a) m (splitRe rest),
        coeff_modulus_cons (imG a) m (splitIm rest)]
      rw [conj_reG a, conj_imG a, conj_splitRe rest, conj_splitIm rest]
      have hq : coeffOf (modulusSq rest) t =
          coeffOf (modulusSq (splitRe rest)) t + coeffOf (modulusSq (splitIm rest)) t := by
        rw [← partSquares_modulus, ih]
      have hc :
          coeffOf (mulMono a m (conjP rest) ++ pmul rest (single (Gauss.conj a) m)) t =
            coeffOf (mulMono (reG a) m (splitRe rest) ++
                pmul (splitRe rest) (single (reG a) m)) t +
              coeffOf (mulMono (imG a) m (splitIm rest) ++
                pmul (splitIm rest) (single (imG a) m)) t := by
        rw [coeff_cross a m rest t,
          coeffOf_append
            (mulMono (reG a) m (splitRe rest) ++ pmul (splitRe rest) (single (reG a) m))
            (mulMono (imG a) m (splitIm rest) ++ pmul (splitIm rest) (single (imG a) m))]
      have hd := diag_parts a (m.mul m = t)
      exact arrange_modulus _ _ _ _ _ _ _ _ _ hd hc hq

theorem im_reG (z : Gauss) : (reG z).im = 0 := rfl

theorem im_imG (z : Gauss) : (imG z).im = 0 := rfl

/-- Ogni testa di `splitRe` o `splitIm` è un razionale. -/
def headsReal : Poly → Prop
  | [] => True
  | (a, _) :: rest => a.im = 0 ∧ headsReal rest

theorem coeff_headsReal (p : Poly) (t : Mono) (h : headsReal p) :
    (coeffOf p t).im = 0 := by
  induction p with
  | nil => simp [coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases h with ⟨ha, hr⟩
      rw [coeffOf, Gauss.im_add]
      by_cases hm : m = t
      · rw [ite_eq_left hm, ha, ih hr, Rat.zero_add]
      · rw [ite_eq_right hm, Gauss.im_zero, ih hr, Rat.zero_add]

theorem splitRe_real (p : Poly) : headsReal (splitRe p) := by
  induction p with
  | nil => exact trivial
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [splitRe]
      exact ⟨im_reG a, ih⟩

theorem splitIm_real (p : Poly) : headsReal (splitIm p) := by
  induction p with
  | nil => exact trivial
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [splitIm]
      exact ⟨im_imG a, ih⟩

theorem factor_real (a : Gauss) (m : Mono) (q : Poly) (t : Mono)
    (ha : a.im = 0) (hq : ∀ u, (coeffOf q u).im = 0) :
    (factor a m q t).im = 0 := by
  cases hsub : subExp t m with
  | none => simp [factor, hsub]
  | some k =>
    simp [factor, hsub, Gauss.im_mul, ha, hq k]
    exact Rat.zero_add 0

theorem coeff_mulMono_real (a : Gauss) (m : Mono) (q : Poly) (t : Mono)
    (ha : a.im = 0) (hq : ∀ u, (coeffOf q u).im = 0) :
    (coeffOf (mulMono a m q) t).im = 0 := by
  rw [coeffOf_mulMono]
  exact factor_real a m q t ha hq

theorem coeff_pmul_real (p q : Poly) (t : Mono)
    (hp : headsReal p) (hq : ∀ u, (coeffOf q u).im = 0) :
    (coeffOf (pmul p q) t).im = 0 := by
  induction p with
  | nil => simp [pmul, Universe.Quotient.mul, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases hp with ⟨ha, hr⟩
      rw [show pmul ((a, m) :: rest) q = mulMono a m q ++ pmul rest q from rfl,
        coeffOf_append, Gauss.im_add,
        coeff_mulMono_real a m q t ha hq, ih hr, Rat.zero_add]

/-- Ogni coefficiente di `z · conj(z)` è razionale. -/
theorem modulus_imag_zero (p : Poly) (t : Mono) :
    (coeffOf (modulusSq p) t).im = 0 := by
  rw [modulus_squares, partSquares, coeffOf_append, Gauss.im_add]
  rw [coeff_pmul_real (splitRe p) (splitRe p) t (splitRe_real p)
      (fun u => coeff_headsReal (splitRe p) u (splitRe_real p)),
    coeff_pmul_real (splitIm p) (splitIm p) t (splitIm_real p)
      (fun u => coeff_headsReal (splitIm p) u (splitIm_real p)),
    Rat.zero_add]

/-! ### Le probabilità sono reali -/

/-- Ogni peso di Born ha coefficienti razionali. Vale per ampiezze arbitrarie. -/
theorem columnBorn_real (z : Poly) (t : Mono) :
    (coeffOf (columnBorn z) t).im = 0 :=
  modulus_imag_zero z t

/-- `P(0)` e `P(1)` di `Φ|0⟩` hanno coefficienti razionali. -/
theorem ground_prob_real (t : Mono) :
    (coeffOf groundP0 t).im = 0 ∧ (coeffOf groundP1 t).im = 0 :=
  ⟨columnBorn_real evolution.a00 t, columnBorn_real evolution.a10 t⟩

/-! ### Proiettore computazionale -/

/-- `Π₀ = diag(1, 0)`. -/
def pi0 : Mat := ⟨single 1 Mono.one, [], [], []⟩

/-- `⟨ψ|Π₀|ψ⟩ = |α|²` per ogni coppia di ampiezze. -/
theorem projector_born (α β : Poly) :
    polySame (sandwich pi0 α β) (columnBorn α) := by
  intro t
  have h0 : pmul pi0.a00 α ++ pmul pi0.a01 β = α ++ [] := by
    rw [pi0, one_pmul]
    rfl
  have h1 : pmul pi0.a10 α ++ pmul pi0.a11 β = [] := by
    rw [pi0]
    rfl
  rw [sandwich, h0, h1, coeffOf_append, pmul_nil, coeffOf_nil, Gauss.add_zero,
    coeff_mul_append_right, coeffOf_append, pmul_nil, coeffOf_nil, Gauss.add_zero,
    columnBorn, coeff_mul_comm]

/-! ### Sfera, con cofattore proprio -/

def ar1 : Mono := {Mono.one with ar := 1}
def ai1 : Mono := {Mono.one with ai := 1}
def br1 : Mono := {Mono.one with br := 1}
def bi1 : Mono := {Mono.one with bi := 1}

/-- Ampiezza generica `ar + i ai`. -/
def genericA : Poly := single 1 ar1 ++ single Gauss.i ai1

/-- Ampiezza generica `br + i bi`. -/
def genericB : Poly := single 1 br1 ++ single Gauss.i bi1

theorem mono_mul_left_cancel {m a b : Mono} (h : m.mul a = m.mul b) : a = b := by
  ext
  · exact Nat.add_left_cancel (congrArg Mono.c h)
  · exact Nat.add_left_cancel (congrArg Mono.s h)
  · exact Nat.add_left_cancel (congrArg Mono.nx h)
  · exact Nat.add_left_cancel (congrArg Mono.ny h)
  · exact Nat.add_left_cancel (congrArg Mono.nz h)
  · exact Nat.add_left_cancel (congrArg Mono.ar h)
  · exact Nat.add_left_cancel (congrArg Mono.ai h)
  · exact Nat.add_left_cancel (congrArg Mono.br h)
  · exact Nat.add_left_cancel (congrArg Mono.bi h)

theorem factor_lin (a : Gauss) (m : Mono) (c d : Gauss) (p q t : Mono) :
    factor a m (single c p ++ single d q) t =
      (if m.mul p = t then a * c else 0) + (if m.mul q = t then a * d else 0) := by
  cases hsub : subExp t m with
  | none =>
    have hp : m.mul p ≠ t := by
      intro eq
      have hs := subExp_mul m p
      rw [eq] at hs
      rw [hs] at hsub
      cases hsub
    have hq : m.mul q ≠ t := by
      intro eq
      have hs := subExp_mul m q
      rw [eq] at hs
      rw [hs] at hsub
      cases hsub
    rw [factor, hsub, ite_eq_right hp, ite_eq_right hq, Gauss.zero_add]
  | some k =>
    have ht : m.mul k = t := mul_subExp hsub
    simp only [factor, hsub]
    rw [coeffOf_append, coeff_single_eq, coeff_single_eq, Gauss.mul_add]
    by_cases hp : p = k <;> by_cases hq : q = k
    · have hpt : m.mul p = t := by rw [hp, ht]
      have hqt : m.mul q = t := by rw [hq, ht]
      rw [ite_eq_left hp, ite_eq_left hq, ite_eq_left hpt, ite_eq_left hqt]
    · have hpt : m.mul p = t := by rw [hp, ht]
      have hqt : m.mul q ≠ t := by
        intro eq
        exact hq (mono_mul_left_cancel (eq.trans ht.symm))
      rw [ite_eq_left hp, ite_eq_right hq, ite_eq_left hpt, ite_eq_right hqt,
        Gauss.mul_zero]
    · have hpt : m.mul p ≠ t := by
        intro eq
        exact hp (mono_mul_left_cancel (eq.trans ht.symm))
      have hqt : m.mul q = t := by rw [hq, ht]
      rw [ite_eq_right hp, ite_eq_left hq, ite_eq_right hpt, ite_eq_left hqt,
        Gauss.mul_zero, Gauss.zero_add]
    · have hpt : m.mul p ≠ t := by
        intro eq
        exact hp (mono_mul_left_cancel (eq.trans ht.symm))
      have hqt : m.mul q ≠ t := by
        intro eq
        exact hq (mono_mul_left_cancel (eq.trans ht.symm))
      rw [ite_eq_right hp, ite_eq_right hq, ite_eq_right hpt, ite_eq_right hqt,
        Gauss.mul_zero, Gauss.zero_add]

theorem coeff_lin_mod (a b : Gauss) (m n t : Mono) :
    coeffOf (pmul (single (Gauss.conj a) m ++ single (Gauss.conj b) n)
        (single a m ++ single b n)) t =
      ((if m.mul m = t then Gauss.conj a * a else 0) +
          (if m.mul n = t then Gauss.conj a * b else 0)) +
        ((if n.mul m = t then Gauss.conj b * a else 0) +
          (if n.mul n = t then Gauss.conj b * b else 0)) := by
  rw [coeffOf_mul]
  have hl : single (Gauss.conj a) m ++ single (Gauss.conj b) n =
      (Gauss.conj a, m) :: (Gauss.conj b, n) :: [] := by simp [single]
  rw [hl]
  simp only [coeffSum, factor_lin, Gauss.add_zero]

theorem ar1_sq : ar1.mul ar1 = arSq := by ext <;> rfl
theorem ai1_sq : ai1.mul ai1 = aiSq := by ext <;> rfl
theorem br1_sq : br1.mul br1 = brSq := by ext <;> rfl
theorem bi1_sq : bi1.mul bi1 = biSq := by ext <;> rfl

theorem cross_cancel (cond : Prop) [Decidable cond] :
    (if cond then Gauss.i else 0) + (if cond then -Gauss.i else 0) = 0 := by
  by_cases h : cond
  · rw [ite_eq_left h, ite_eq_left h, Gauss.add_neg_cancel]
  · rw [ite_eq_right h, ite_eq_right h, Gauss.zero_add]

theorem cancel_cross (a b c d : Gauss) (h : b + c = 0) : (a + b) + (c + d) = a + d := by
  rw [Gauss.add_assoc, ← Gauss.add_assoc b c d, h, Gauss.zero_add]

/-- `|ar + i ai|²` ha i coefficienti di `ar² + ai²`. Lo stesso per `br`, `bi`. -/
theorem lin_imag_mod (u v sqU sqV : Mono) (hu : u.mul u = sqU) (hv : v.mul v = sqV) (t : Mono) :
    coeffOf (pmul (conjP (single 1 u ++ single Gauss.i v)) (single 1 u ++ single Gauss.i v)) t =
      coeffOf (single 1 sqU ++ single 1 sqV) t := by
  have hc : conjP (single 1 u ++ single Gauss.i v) = single 1 u ++ single (-Gauss.i) v := by
    simp [conjP, single, conj_one, conj_i]
  rw [hc]
  have hmod := coeff_lin_mod (1 : Gauss) Gauss.i u v t
  rw [conj_one, conj_i, Gauss.one_mul, Gauss.mul_one, minus_i_mul_i, hu, hv,
    Mono.mul_comm v u] at hmod
  rw [hmod, coeffOf_append, coeff_single_eq, coeff_single_eq]
  exact cancel_cross _ _ _ _ (by
    rw [Gauss.one_mul]
    exact cross_cancel (u.mul v = t))

theorem generic_norm (t : Mono) :
    coeffOf (normAmp genericA genericB) t = coeffOf amp t := by
  rw [normAmp, genericA, genericB, coeffOf_append,
    lin_imag_mod ar1 ai1 arSq aiSq ar1_sq ai1_sq,
    lin_imag_mod br1 bi1 brSq biSq br1_sq bi1_sq, amp,
    coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append]
  exact (Gauss.add_assoc _ _ _).symm

/-- Appartenenza all'ideale `(gC, gN, gA)`, con tre cofattori. Non estende `inIdeal`. -/
def inIdeal3 (p : Poly) : Prop :=
  ∃ fc fn fa, ∀ t,
    coeffOf p t = coeffOf (pmul fc gC ++ pmul fn gN ++ pmul fa gA) t

theorem gA_as_psub : gA = psub amp (single 1 Mono.one) := by
  rw [gA, psub]
  rfl

theorem generic_sphere :
    polySame (psub (normAmp genericA genericB) (single 1 Mono.one)) gA := by
  intro t
  rw [coeff_psub, generic_norm, ← coeff_psub, ← gA_as_psub]

/-- Sullo stato generico, `ψ†(U†U)ψ − 1` ha cofattori `gC`, `gN` e `gA`. -/
theorem sphere_prob_sum :
    inIdeal3 (psub (sandwich (matMul (matDagger evolution) evolution) genericA genericB)
      (single 1 Mono.one)) := by
  rcases evolution_norm genericA genericB with ⟨fc, fn, hδ⟩
  refine ⟨fc, fn, single 1 Mono.one, ?_⟩
  intro t
  have hsplit :=
    polySame_psub_trans
      (sandwich (matMul (matDagger evolution) evolution) genericA genericB)
      (normAmp genericA genericB) (single 1 Mono.one) t
  have hga : coeffOf gA t = coeffOf (pmul (single (1 : Gauss) Mono.one) gA) t := by
    rw [one_pmul]
  rw [hsplit, coeffOf_append, hδ t, generic_sphere, hga, ← coeffOf_append]

/-! ### Il modulo letterale e il sandwich -/

/-- `|γ₀|² + |γ₁|²`, con `γ = Uψ` e l'ordine `z · conj(z)`. -/
def literalNorm (U : Mat) (α β : Poly) : Poly :=
  columnBorn (pmul U.a00 α ++ pmul U.a01 β) ++
    columnBorn (pmul U.a10 α ++ pmul U.a11 β)

theorem polySame_mul_comm (p q : Poly) : polySame (pmul p q) (pmul q p) :=
  fun t => coeff_mul_comm p q t

theorem polySame_mul_append_right (p q r : Poly) :
    polySame (pmul p (q ++ r)) (pmul p q ++ pmul p r) :=
  fun t => coeff_mul_append_right p q r t

theorem polySame_mul_append4 (r a b c d : Poly) :
    polySame (pmul r ((a ++ b) ++ (c ++ d)))
      ((pmul r a ++ pmul r b) ++ (pmul r c ++ pmul r d)) :=
  polySame.trans (polySame_mul_append_right r (a ++ b) (c ++ d))
    (polySame_append (polySame_mul_append_right r a b)
      (polySame_mul_append_right r c d))

theorem polySame_psub {p p' q q' : Poly} (hp : polySame p p') (hq : polySame q q') :
    polySame (psub p q) (psub p' q') :=
  polySame_append hp (polySame_pneg hq)

theorem inIdeal3_polySame {p q : Poly} (h : polySame p q) (hq : inIdeal3 q) : inIdeal3 p := by
  rcases hq with ⟨fc, fn, fa, hq⟩
  exact ⟨fc, fn, fa, fun t => (h t).trans (hq t)⟩

/-- `conj(y) · ((conj(q) · p) · x)`. Stesso multinsieme di `(p · x) · (conj(q) · conj(y))`. -/
def braTerm (p q x y : Poly) : Poly :=
  pmul (conjP y) (pmul (pmul (conjP q) p) x)

/-- I due ordini di quattro fattori hanno gli stessi coefficienti. -/
theorem term_align (p q x y : Poly) :
    polySame
      (pmul (pmul p x) (pmul (conjP q) (conjP y)))
      (braTerm p q x y) :=
  polySame.trans
    (polySame_pmul_right (polySame_mul_comm (conjP q) (conjP y)) (pmul p x))
    (polySame.trans
      (polySame.symm (polySame_pmul_assoc (pmul p x) (conjP y) (conjP q)))
      (polySame.trans
        (polySame_pmul_left (polySame_mul_comm (pmul p x) (conjP y)) (conjP q))
        (polySame.trans
          (polySame_pmul_assoc (conjP y) (pmul p x) (conjP q))
          (polySame.trans
            (polySame_pmul_right (polySame_mul_comm (pmul p x) (conjP q)) (conjP y))
            (polySame_pmul_right
              (polySame.symm (polySame_pmul_assoc (conjP q) p x)) (conjP y))))))

theorem columnBorn_append (p q : Poly) :
    polySame (columnBorn (p ++ q))
      ((pmul p (conjP p) ++ pmul p (conjP q)) ++ (pmul q (conjP p) ++ pmul q (conjP q))) := by
  rw [columnBorn, conj_append, pmul_append_left]
  exact polySame_append
    (polySame_mul_append_right p (conjP p) (conjP q))
    (polySame_mul_append_right q (conjP p) (conjP q))

theorem align_ket (p q x y : Poly) :
    polySame (pmul (pmul p x) (conjP (pmul q y))) (braTerm p q x y) := by
  rw [conj_pmul]
  exact term_align p q x y

theorem columnBorn_pair (p q x y : Poly) :
    polySame (columnBorn (pmul p x ++ pmul q y))
      ((braTerm p p x x ++ braTerm p q x y) ++ (braTerm q p y x ++ braTerm q q y y)) :=
  polySame.trans (columnBorn_append (pmul p x) (pmul q y))
    (polySame_append
      (polySame_append (align_ket p p x x) (align_ket p q x y))
      (polySame_append (align_ket q p y x) (align_ket q q y y)))

theorem uu_a00 (U : Mat) :
    (matMul (matDagger U) U).a00 =
      pmul (conjP U.a00) U.a00 ++ pmul (conjP U.a10) U.a10 := rfl

theorem uu_a01 (U : Mat) :
    (matMul (matDagger U) U).a01 =
      pmul (conjP U.a00) U.a01 ++ pmul (conjP U.a10) U.a11 := rfl

theorem uu_a10 (U : Mat) :
    (matMul (matDagger U) U).a10 =
      pmul (conjP U.a01) U.a00 ++ pmul (conjP U.a11) U.a10 := rfl

theorem uu_a11 (U : Mat) :
    (matMul (matDagger U) U).a11 =
      pmul (conjP U.a01) U.a01 ++ pmul (conjP U.a11) U.a11 := rfl

theorem sandwich_expand (U : Mat) (α β : Poly) :
    polySame (sandwich (matMul (matDagger U) U) α β)
      (((braTerm U.a00 U.a00 α α ++ braTerm U.a10 U.a10 α α) ++
          (braTerm U.a01 U.a00 β α ++ braTerm U.a11 U.a10 β α)) ++
        ((braTerm U.a00 U.a01 α β ++ braTerm U.a10 U.a11 α β) ++
          (braTerm U.a01 U.a01 β β ++ braTerm U.a11 U.a11 β β))) := by
  have hlist :
      sandwich (matMul (matDagger U) U) α β =
        pmul (conjP α)
            ((pmul (pmul (conjP U.a00) U.a00) α ++ pmul (pmul (conjP U.a10) U.a10) α) ++
              (pmul (pmul (conjP U.a00) U.a01) β ++ pmul (pmul (conjP U.a10) U.a11) β)) ++
          pmul (conjP β)
            ((pmul (pmul (conjP U.a01) U.a00) α ++ pmul (pmul (conjP U.a11) U.a10) α) ++
              (pmul (pmul (conjP U.a01) U.a01) β ++ pmul (pmul (conjP U.a11) U.a11) β)) := by
    rw [sandwich, uu_a00, uu_a01, uu_a10, uu_a11, pmul_append_left, pmul_append_left,
      pmul_append_left, pmul_append_left]
  rw [hlist]
  exact polySame_append
    (polySame_mul_append4 (conjP α)
      (pmul (pmul (conjP U.a00) U.a00) α)
      (pmul (pmul (conjP U.a10) U.a10) α)
      (pmul (pmul (conjP U.a00) U.a01) β)
      (pmul (pmul (conjP U.a10) U.a11) β))
    (polySame_mul_append4 (conjP β)
      (pmul (pmul (conjP U.a01) U.a00) α)
      (pmul (pmul (conjP U.a11) U.a10) α)
      (pmul (pmul (conjP U.a01) U.a01) β)
      (pmul (pmul (conjP U.a11) U.a11) β))

theorem coeff_append4 (a b c d : Poly) (t : Mono) :
    coeffOf ((a ++ b) ++ (c ++ d)) t =
      (coeffOf a t + coeffOf b t) + (coeffOf c t + coeffOf d t) := by
  rw [coeffOf_append, coeffOf_append, coeffOf_append]

theorem coeff_two_append4 (a b c d e f g h : Poly) (t : Mono) :
    coeffOf (((a ++ b) ++ (c ++ d)) ++ ((e ++ f) ++ (g ++ h))) t =
      ((coeffOf a t + coeffOf b t) + (coeffOf c t + coeffOf d t)) +
        ((coeffOf e t + coeffOf f t) + (coeffOf g t + coeffOf h t)) := by
  rw [coeffOf_append, coeff_append4, coeff_append4]

theorem gauss8_literal_sandwich (t00 t01 t10 t11 s00 s01 s10 s11 : Gauss) :
    ((t00 + t01) + (t10 + t11)) + ((s00 + s01) + (s10 + s11)) =
      ((t00 + s00) + (t10 + s10)) + ((t01 + s01) + (t11 + s11)) := by
  ext <;> simp <;> grind

/-- Per ogni matrice, `|Uψ|²` e `ψ†(U†U)ψ` hanno gli stessi coefficienti. -/
theorem literal_sandwich (U : Mat) (α β : Poly) :
    polySame (literalNorm U α β) (sandwich (matMul (matDagger U) U) α β) := by
  intro t
  rw [literalNorm,
    polySame_append (columnBorn_pair U.a00 U.a01 α β) (columnBorn_pair U.a10 U.a11 α β) t,
    sandwich_expand U α β t, coeff_two_append4, coeff_two_append4]
  exact gauss8_literal_sandwich
    (coeffOf (braTerm U.a00 U.a00 α α) t)
    (coeffOf (braTerm U.a00 U.a01 α β) t)
    (coeffOf (braTerm U.a01 U.a00 β α) t)
    (coeffOf (braTerm U.a01 U.a01 β β) t)
    (coeffOf (braTerm U.a10 U.a10 α α) t)
    (coeffOf (braTerm U.a10 U.a11 α β) t)
    (coeffOf (braTerm U.a11 U.a10 β α) t)
    (coeffOf (braTerm U.a11 U.a11 β β) t)

/-- `‖ψ‖²` nell'ordine `z · conj(z)` ha i coefficienti di `normAmp`. -/
theorem born_norm (α β : Poly) :
    polySame (columnBorn α ++ columnBorn β) (normAmp α β) := by
  intro t
  rw [normAmp, coeffOf_append, coeffOf_append, columnBorn_comm α, columnBorn_comm β]

/-- `‖Uψ‖² − ‖ψ‖²`, modulo letterale, sta in `(gC, gN)`. -/
theorem literal_evolution_norm (α β : Poly) :
    inIdeal (psub (literalNorm evolution α β) (columnBorn α ++ columnBorn β)) := by
  exact inIdeal_polySame
    (polySame_psub (literal_sandwich evolution α β) (born_norm α β))
    (evolution_norm α β)

/-- Sullo stato generico, `‖Uψ‖² − 1` sta in `(gC, gN, gA)`. -/
theorem literal_sphere :
    inIdeal3 (psub (literalNorm evolution genericA genericB) (single 1 Mono.one)) := by
  exact inIdeal3_polySame
    (polySame_psub (literal_sandwich evolution genericA genericB) (polySame_refl _))
    sphere_prob_sum

/-! ### Assi x e z -/

def optionMul : Option Mono → Option Mono → Option Mono
  | some m, some n => some (m.mul n)
  | _, _ => none

/-- `nx = 1`, `ny = nz = 0`. L'esponente di `nx` si azzera. -/
def keepX (m : Mono) : Option Mono :=
  if m.ny = 0 ∧ m.nz = 0 then some {m with nx := 0} else none

/-- `nz = 1`, `nx = ny = 0`. L'esponente di `nz` si azzera. -/
def keepZ (m : Mono) : Option Mono :=
  if m.nx = 0 ∧ m.ny = 0 then some {m with nz := 0} else none

def specPoly (keep : Mono → Option Mono) : Poly → Poly
  | [] => []
  | (a, m) :: rest =>
    match keep m with
    | none => specPoly keep rest
    | some k => (a, k) :: specPoly keep rest

theorem keepX_mul (m n : Mono) : keepX (m.mul n) = optionMul (keepX m) (keepX n) := by
  unfold keepX optionMul
  by_cases hmy : m.ny = 0 <;> by_cases hmz : m.nz = 0 <;>
      by_cases hny : n.ny = 0 <;> by_cases hnz : n.nz = 0 <;>
      simp [Mono.mul, hmy, hmz, hny, hnz, Nat.add_eq_zero_iff] <;>
      (try (congr 1; ext <;> rfl))

theorem keepZ_mul (m n : Mono) : keepZ (m.mul n) = optionMul (keepZ m) (keepZ n) := by
  unfold keepZ optionMul
  by_cases hmx : m.nx = 0 <;> by_cases hmy : m.ny = 0 <;>
      by_cases hnx : n.nx = 0 <;> by_cases hny : n.ny = 0 <;>
      simp [Mono.mul, hmx, hmy, hnx, hny, Nat.add_eq_zero_iff] <;>
      (try (congr 1; ext <;> rfl))

theorem spec_append (keep : Mono → Option Mono) (p q : Poly) :
    specPoly keep (p ++ q) = specPoly keep p ++ specPoly keep q := by
  induction p with
  | nil => simp [specPoly]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, specPoly, ih]
      cases keep m with
      | none => rfl
      | some k => simp

theorem polySame_cons (a : Gauss) (m : Mono) {p q : Poly} (h : polySame p q) :
    polySame ((a, m) :: p) ((a, m) :: q) := by
  intro t
  simp only [coeffOf]
  rw [h t]

theorem spec_conj (keep : Mono → Option Mono) (p : Poly) :
    specPoly keep (conjP p) = conjP (specPoly keep p) := by
  induction p with
  | nil => simp [specPoly, conjP]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [conjP, specPoly]
      cases keep m with
      | none => exact ih
      | some k => simp only [conjP, ih]

theorem spec_mulMono_drop {keep : Mono → Option Mono}
    (hmul : ∀ m n, keep (m.mul n) = optionMul (keep m) (keep n))
    (a : Gauss) (m : Mono) (q : Poly) (hm : keep m = none) :
    polySame (specPoly keep (mulMono a m q)) [] := by
  induction q with
  | nil =>
    simp [mulMono, specPoly]
    exact polySame_refl _
  | cons head rest ih =>
    cases head with
    | mk b n =>
      have hprod : keep (m.mul n) = none := by rw [hmul, hm]; rfl
      simp only [mulMono, specPoly, hprod]
      exact ih

theorem spec_mulMono_keep {keep : Mono → Option Mono}
    (hmul : ∀ m n, keep (m.mul n) = optionMul (keep m) (keep n))
    (a : Gauss) (m k : Mono) (q : Poly) (hm : keep m = some k) :
    polySame (specPoly keep (mulMono a m q)) (mulMono a k (specPoly keep q)) := by
  induction q with
  | nil =>
    simp [mulMono, specPoly]
    exact polySame_refl _
  | cons head rest ih =>
    cases head with
    | mk b n =>
      cases hn : keep n with
      | none =>
        have hprod : keep (m.mul n) = none := by rw [hmul, hm, hn]; rfl
        simp only [mulMono, specPoly, hprod, hn]
        exact ih
      | some k' =>
        have hprod : keep (m.mul n) = some (k.mul k') := by rw [hmul, hm, hn]; rfl
        simp only [mulMono, specPoly, hprod, hn]
        exact polySame_cons (a * b) (k.mul k') ih

theorem spec_pmul {keep : Mono → Option Mono}
    (hmul : ∀ m n, keep (m.mul n) = optionMul (keep m) (keep n))
    (p q : Poly) :
    polySame (specPoly keep (pmul p q)) (pmul (specPoly keep p) (specPoly keep q)) := by
  induction p with
  | nil =>
    simp [pmul, Universe.Quotient.mul, specPoly]
    exact polySame_refl _
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show pmul ((a, m) :: rest) q = mulMono a m q ++ pmul rest q from rfl, spec_append]
      cases hm : keep m with
      | none =>
        refine polySame.trans (polySame_append (spec_mulMono_drop hmul a m q hm) ih) ?_
        simp only [specPoly, hm]
        exact polySame_nil_append _
      | some k =>
        refine polySame.trans (polySame_append (spec_mulMono_keep hmul a m k q hm) ih) ?_
        simp only [specPoly, hm, pmul, Universe.Quotient.mul]
        exact polySame_refl _

theorem specX_conj (p : Poly) :
    specPoly keepX (conjP p) = conjP (specPoly keepX p) :=
  spec_conj keepX p

theorem specZ_conj (p : Poly) :
    specPoly keepZ (conjP p) = conjP (specPoly keepZ p) :=
  spec_conj keepZ p

theorem specX_pmul (p q : Poly) :
    polySame (specPoly keepX (pmul p q)) (pmul (specPoly keepX p) (specPoly keepX q)) :=
  spec_pmul keepX_mul p q

theorem specZ_pmul (p q : Poly) :
    polySame (specPoly keepZ (pmul p q)) (pmul (specPoly keepZ p) (specPoly keepZ q)) :=
  spec_pmul keepZ_mul p q

/-- `spec` del modulo `z · conj(z)` è il modulo dell'ampiezza già specializzata. -/
theorem spec_columnBorn {keep : Mono → Option Mono}
    (hmul : ∀ m n, keep (m.mul n) = optionMul (keep m) (keep n)) (z : Poly) :
    polySame (specPoly keep (columnBorn z)) (columnBorn (specPoly keep z)) := by
  refine polySame.trans (spec_pmul hmul z (conjP z)) ?_
  rw [columnBorn]
  refine polySame_pmul_right ?_ (specPoly keep z)
  intro t
  rw [spec_conj]

theorem evolution_a00_bin :
    evolution.a00 = single (1 : Gauss) c1 ++ single (-Gauss.i) (s1.mul nz1) := by
  unfold evolution lin
  rw [pmul_one, gamma, hamiltonian, h00, pmul_single_single, Gauss.mul_one, List.append_nil, cP]

theorem evolution_a10_bin :
    evolution.a10 = single (-Gauss.i) (s1.mul nx1) ++ single (1 : Gauss) (s1.mul ny1) := by
  have ha : evolution.a10 = pmul gamma h10 := by
    unfold evolution lin hamiltonian
    rfl
  rw [ha, gamma, h10]
  simp [pmul, Universe.Quotient.mul, mulMono, single, List.append_nil, Gauss.mul_one,
    minus_i_mul_i]

theorem specX_a00 : specPoly keepX evolution.a00 = single (1 : Gauss) c1 := by
  rw [evolution_a00_bin, spec_append]
  simp [specPoly, keepX, single, c1, s1, nz1, Mono.mul, Mono.one]

theorem specX_a10 : specPoly keepX evolution.a10 = single (-Gauss.i) s1 := by
  rw [evolution_a10_bin, spec_append]
  simp [specPoly, keepX, single, s1, nx1, ny1, Mono.mul, Mono.one]

theorem specZ_a00 :
    specPoly keepZ evolution.a00 = single (1 : Gauss) c1 ++ single (-Gauss.i) s1 := by
  rw [evolution_a00_bin, spec_append]
  simp [specPoly, keepZ, single, c1, s1, nz1, Mono.mul, Mono.one]

theorem specZ_a10 : specPoly keepZ evolution.a10 = [] := by
  rw [evolution_a10_bin, spec_append]
  simp [specPoly, keepZ, single, s1, nx1, ny1, Mono.mul, Mono.one]

/-- `1 − s²`. -/
def oneMinusS : Poly := single (1 : Gauss) Mono.one ++ single (-1) sSq

theorem gneg_add (z w : Gauss) : -(z + w) = -z + -w := by
  ext <;> simp <;> grind

theorem gneg_zero : -((0 : Gauss)) = 0 := by
  ext <;> simp <;> grind

theorem neg_if_one (cond : Prop) [Decidable cond] :
    -((if cond then (1 : Gauss) else 0)) = if cond then -1 else 0 := by
  by_cases h : cond
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, gneg_zero]

theorem neg_if_neg_one (cond : Prop) [Decidable cond] :
    -((if cond then (-1 : Gauss) else 0)) = if cond then 1 else 0 := by
  by_cases h : cond
  · rw [ite_eq_left h, ite_eq_left h, Gauss.neg_neg]
  · rw [ite_eq_right h, ite_eq_right h, gneg_zero]

theorem born_c :
    columnBorn (single (1 : Gauss) c1) = single 1 cSq ++ [] := by
  rw [columnBorn, conjP_real, pmul_single_single, Gauss.mul_one, c1_sq]

theorem born_minus_i_s :
    columnBorn (single (-Gauss.i) s1) = single 1 sSq ++ [] := by
  rw [columnBorn, conjP_neg_imag, pmul_single_single, minus_i_mul_i, s1_sq]

theorem axis_x_prob1 :
    polySame (columnBorn (specPoly keepX evolution.a10)) (single (1 : Gauss) sSq) := by
  intro t
  rw [specX_a10, born_minus_i_s, List.append_nil]

theorem specX_nxSq : specPoly keepX (single (1 : Gauss) nxSq) = single 1 Mono.one := by
  simp [specPoly, keepX, single, nxSq, Mono.one]

theorem specX_nySq : specPoly keepX (single (1 : Gauss) nySq) = [] := by
  simp [specPoly, keepX, single, nySq]

theorem specX_nzSq : specPoly keepX (single (1 : Gauss) nzSq) = [] := by
  simp [specPoly, keepX, single, nzSq]

theorem specX_const (a : Gauss) :
    specPoly keepX (single a Mono.one) = single a Mono.one := by
  simp [specPoly, keepX, single, Mono.one]

/-- Lungo x, `nx ↦ 1` e `ny = nz = 0`: i coefficienti di `gN` sono zero. -/
theorem axis_x_gn : polySame (specPoly keepX gN) [] := by
  intro t
  rw [gN, spec_append, spec_append, spec_append, specX_nxSq, specX_nySq, specX_nzSq,
    specX_const, List.append_nil, List.append_nil, coeffOf_append, coeff_single_eq,
    coeff_single_eq, coeffOf_nil]
  by_cases h : Mono.one = t
  · rw [ite_eq_left h, ite_eq_left h, Gauss.add_neg_cancel]
  · rw [ite_eq_right h, ite_eq_right h, Gauss.zero_add]

theorem axis_x_prob0 :
    polySame (psub (columnBorn (specPoly keepX evolution.a00)) oneMinusS) gC := by
  intro t
  rw [specX_a00, born_c, List.append_nil, oneMinusS, coeff_psub, gC,
    coeffOf_append, coeffOf_append, coeffOf_append,
    coeff_single_eq, coeff_single_eq, coeff_single_eq, coeff_single_eq, coeff_single_eq,
    gneg_add, neg_if_one (Mono.one = t), neg_if_neg_one (sSq = t),
    Gauss.add_comm (if Mono.one = t then -1 else 0) (if sSq = t then 1 else 0), ← Gauss.add_assoc]

theorem born_circle :
    polySame (columnBorn (single (1 : Gauss) c1 ++ single (-Gauss.i) s1))
      (single 1 cSq ++ single 1 sSq) := by
  intro t
  have hmod := coeff_lin_mod (1 : Gauss) (-Gauss.i) c1 s1 t
  rw [conj_one, conj_neg_i, Gauss.one_mul, Gauss.mul_one, i_mul_minus_i, c1_sq, s1_sq,
    Mono.mul_comm s1 c1] at hmod
  rw [columnBorn, conj_append, conjP_real, conjP_neg_imag, coeff_mul_comm, hmod,
    coeffOf_append, coeff_single_eq, coeff_single_eq]
  exact cancel_cross _ _ _ _ (by
    rw [Gauss.one_mul]
    by_cases h : c1.mul s1 = t
    · rw [ite_eq_left h, ite_eq_left h, Gauss.neg_add_cancel]
    · rw [ite_eq_right h, ite_eq_right h, Gauss.zero_add])

/-- Lungo z la seconda ampiezza è il polinomio zero, quindi `P(1) = 0`. -/
theorem axis_z_prob1 : columnBorn (specPoly keepZ evolution.a10) = [] := by
  rw [specZ_a10, columnBorn, conjP]
  rfl

theorem axis_z_prob0 :
    polySame (psub (columnBorn (specPoly keepZ evolution.a00)) (single 1 Mono.one)) gC := by
  intro t
  rw [specZ_a00, coeff_psub, born_circle, gC, coeffOf_append, coeffOf_append, coeffOf_append,
    coeff_single_eq, coeff_single_eq, coeff_single_eq, coeff_single_eq, neg_if_one (Mono.one = t)]

/-- I pesi di Born già calcolati, poi specializzati. È il polinomio che Python sostituisce. -/
theorem axis_x_born1 :
    polySame (specPoly keepX groundP1) (single (1 : Gauss) sSq) :=
  polySame.trans (by rw [groundP1]; exact spec_columnBorn keepX_mul evolution.a10) axis_x_prob1

theorem axis_x_born0 :
    polySame (psub (specPoly keepX groundP0) oneMinusS) gC :=
  polySame.trans
    (polySame_psub (by rw [groundP0]; exact spec_columnBorn keepX_mul evolution.a00)
      (polySame_refl _))
    axis_x_prob0

theorem axis_z_born1 : polySame (specPoly keepZ groundP1) [] := by
  refine polySame.trans (by rw [groundP1]; exact spec_columnBorn keepZ_mul evolution.a10) ?_
  rw [axis_z_prob1]
  exact polySame_refl _

theorem axis_z_born0 :
    polySame (psub (specPoly keepZ groundP0) (single 1 Mono.one)) gC :=
  polySame.trans
    (polySame_psub (by rw [groundP0]; exact spec_columnBorn keepZ_mul evolution.a00)
      (polySame_refl _))
    axis_z_prob0

theorem specZ_nxSq : specPoly keepZ (single (1 : Gauss) nxSq) = [] := by
  simp [specPoly, keepZ, single, nxSq]

theorem specZ_nySq : specPoly keepZ (single (1 : Gauss) nySq) = [] := by
  simp [specPoly, keepZ, single, nySq]

theorem specZ_nzSq : specPoly keepZ (single (1 : Gauss) nzSq) = single 1 Mono.one := by
  simp [specPoly, keepZ, single, nzSq, Mono.one]

theorem specZ_const (a : Gauss) :
    specPoly keepZ (single a Mono.one) = single a Mono.one := by
  simp [specPoly, keepZ, single, Mono.one]

/-- Lungo z, `nz ↦ 1` e `nx = ny = 0`: i coefficienti di `gN` sono zero. -/
theorem axis_z_gn : polySame (specPoly keepZ gN) [] := by
  intro t
  rw [gN, spec_append, spec_append, spec_append, specZ_nxSq, specZ_nySq, specZ_nzSq,
    specZ_const, List.nil_append, List.nil_append, coeffOf_append, coeff_single_eq,
    coeff_single_eq, coeffOf_nil]
  by_cases h : Mono.one = t
  · rw [ite_eq_left h, ite_eq_left h, Gauss.add_neg_cancel]
  · rw [ite_eq_right h, ite_eq_right h, Gauss.zero_add]

/-! ### Punto `c = 3/5`, `s = 4/5`, `n = e_x` -/

def powR (z : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => powR z n * z

/-- Valore di un monomio in `c, s, nx, ny, nz`.
I monomi di `δ` e dei pesi lungo x hanno esponente di ampiezza zero. -/
def monoVal (c s nx ny nz : Rat) (m : Mono) : Rat :=
  powR c m.c * powR s m.s * powR nx m.nx * powR ny m.ny * powR nz m.nz

def evalAt (c s nx ny nz : Rat) : Poly → Gauss
  | [] => 0
  | (a, m) :: rest =>
      ⟨a.re * monoVal c s nx ny nz m, a.im * monoVal c s nx ny nz m⟩
        + evalAt c s nx ny nz rest

def pointC : Rat := (3 : Rat) / 5
def pointS : Rat := (4 : Rat) / 5

theorem eval_append (c s nx ny nz : Rat) (p q : Poly) :
    evalAt c s nx ny nz (p ++ q) = evalAt c s nx ny nz p + evalAt c s nx ny nz q := by
  induction p with
  | nil => simp [evalAt, Gauss.zero_add]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, evalAt, ih]
      rw [← Gauss.add_assoc]

theorem eval_single (c s nx ny nz : Rat) (a : Gauss) (m : Mono) :
    evalAt c s nx ny nz (single a m) =
      ⟨a.re * monoVal c s nx ny nz m, a.im * monoVal c s nx ny nz m⟩ := by
  simp [evalAt, single, Gauss.add_zero]

theorem point_prob1 :
    evalAt pointC pointS 1 0 0 (columnBorn (specPoly keepX evolution.a10)) =
      ⟨(16 : Rat) / 25, 0⟩ := by
  rw [specX_a10, born_minus_i_s, List.append_nil, eval_single]
  ext <;> simp [monoVal, powR, sSq, pointC, pointS] <;> grind

theorem point_prob0 :
    evalAt pointC pointS 1 0 0 (columnBorn (specPoly keepX evolution.a00)) =
      ⟨(9 : Rat) / 25, 0⟩ := by
  rw [specX_a00, born_c, List.append_nil, eval_single]
  ext <;> simp [monoVal, powR, cSq, pointC, pointS] <;> grind

theorem point_gC : evalAt pointC pointS 1 0 0 gC = 0 := by
  rw [gC, eval_append, eval_append, eval_single, eval_single, eval_single]
  simp [monoVal, powR, cSq, sSq, Mono.one, pointC, pointS]
  ext <;> simp <;> grind

theorem point_gN : evalAt pointC pointS 1 0 0 gN = 0 := by
  rw [gN, eval_append, eval_append, eval_append, eval_single, eval_single, eval_single,
    eval_single]
  simp [monoVal, powR, nxSq, nySq, nzSq, Mono.one, pointC, pointS]
  ext <;> simp <;> grind

theorem pmul_single_list (a : Gauss) (m : Mono) (q : Poly) :
    pmul (single a m) q = mulMono a m q ++ [] := by
  simp [pmul, Universe.Quotient.mul, single]

theorem eval_mulMono_single (c s nx ny nz : Rat) (a b : Gauss) (m n : Mono) :
    evalAt c s nx ny nz (mulMono a m (single b n)) =
      ⟨(a * b).re * monoVal c s nx ny nz (m.mul n),
        (a * b).im * monoVal c s nx ny nz (m.mul n)⟩ := by
  simp [mulMono, single, evalAt, Gauss.add_zero]

theorem point_unitary : evalAt pointC pointS 1 0 0 unitaryDefect = 0 := by
  rw [unitaryDefect, eval_append, pmul_single_list, List.append_nil, gN, mulMono_append,
    mulMono_append, mulMono_append, eval_append, eval_append, eval_append, eval_mulMono_single,
    eval_mulMono_single, eval_mulMono_single, eval_mulMono_single, point_gC, Gauss.zero_add]
  simp [monoVal, powR, Mono.mul, sSq, nxSq, nySq, nzSq, Mono.one, pointC, pointS]
  ext <;> simp <;> grind

end Universe.Epistemology
