/-
Dinamica del qubit sul quoziente `c² + s² = 1`, `|n| = 1`.

Le matrici hanno entrate nel polinomio libero. Due entrate sono la stessa classe
quando la differenza sta nell'ideale generato da `gC` e `gN`, con cofattori
espliciti. `Universe.Qubit.expCoeff_hamiltonian` applica `expCoeff` a `H` su
`qubitDyn`: è il lemma che autorizza «U implementa Φ».
-/
import Universe.Quotient
import Universe.Series

namespace Universe.Dynamics

open Universe.Ring
open Universe.Series
open Universe.Quotient hiding mul

abbrev pmul : Poly → Poly → Poly := Universe.Quotient.mul

/-! ### Scalari di Gauss usati dalle matrici -/

theorem Gauss.neg_zero : -(0 : Gauss) = 0 := by
  ext <;> simp <;> grind

theorem Gauss.neg_add (a b : Gauss) : -(a + b) = -a + -b := by
  ext <;> simp <;> grind

theorem Gauss.neg_mul (a b : Gauss) : -(a * b) = -a * b := by
  ext <;> simp <;> grind

theorem Gauss.mul_neg (a b : Gauss) : a * -b = -(a * b) := by
  ext <;> simp <;> grind

theorem Gauss.add_left_comm (a b c : Gauss) : a + (b + c) = b + (a + c) := by
  ext <;> simp <;> grind

theorem Gauss.add_add_add_comm (a b c d : Gauss) : a + b + (c + d) = a + c + (b + d) := by
  ext <;> simp <;> grind

theorem conj_zero : Gauss.conj (0 : Gauss) = 0 := by
  ext <;> simp [Gauss.conj] <;> grind

theorem conj_one : Gauss.conj (1 : Gauss) = 1 := by
  ext <;> simp [Gauss.conj] <;> grind

theorem conj_neg (z : Gauss) : Gauss.conj (-z) = -Gauss.conj z := by
  ext <;> simp [Gauss.conj] <;> grind

theorem conj_add (z w : Gauss) : Gauss.conj (z + w) = Gauss.conj z + Gauss.conj w := by
  ext <;> simp [Gauss.conj] <;> grind

theorem conj_mul (z w : Gauss) : Gauss.conj (z * w) = Gauss.conj z * Gauss.conj w := by
  ext <;> simp [Gauss.conj] <;> grind

theorem conj_conj (z : Gauss) : Gauss.conj (Gauss.conj z) = z := by
  ext <;> simp [Gauss.conj] <;> grind

theorem conj_i : Gauss.conj Gauss.i = -Gauss.i := by
  ext <;> simp [Gauss.conj, Gauss.i] <;> grind

theorem conj_neg_i : Gauss.conj (-Gauss.i) = Gauss.i := by
  ext <;> simp [Gauss.conj, Gauss.i] <;> grind

theorem minus_i_mul_i : (-Gauss.i) * Gauss.i = 1 := by
  ext <;> simp [Gauss.i] <;> grind

theorem i_mul_minus_i : Gauss.i * -Gauss.i = 1 := by
  ext <;> simp [Gauss.i] <;> grind

/-! ### Monomi -/

theorem Mono.mul_comm (m n : Mono) : m.mul n = n.mul m := by
  ext <;> simp [Mono.mul, Nat.add_comm]

theorem Mono.mul_assoc (a b c : Mono) : (a.mul b).mul c = a.mul (b.mul c) := by
  ext <;> simp [Mono.mul, Nat.add_assoc]

theorem Mono.one_mul (m : Mono) : Mono.one.mul m = m := by
  ext <;> simp [Mono.mul, Mono.one, Nat.zero_add]

theorem Mono.mul_one (m : Mono) : m.mul Mono.one = m := by
  ext <;> simp [Mono.mul, Mono.one, Nat.add_zero]

/-! ### Operazioni libere -/

def pneg : Poly → Poly
  | [] => []
  | (a, m) :: rest => (-a, m) :: pneg rest

def scale (z : Gauss) : Poly → Poly
  | [] => []
  | (a, m) :: rest => (z * a, m) :: scale z rest

def conjP : Poly → Poly
  | [] => []
  | (a, m) :: rest => (Gauss.conj a, m) :: conjP rest

def psub (p q : Poly) : Poly := p ++ pneg q

def polySame (p q : Poly) : Prop := ∀ t, coeffOf p t = coeffOf q t

theorem coeff_pneg (p : Poly) (t : Mono) : coeffOf (pneg p) t = -coeffOf p t := by
  induction p with
  | nil => simp [pneg, coeffOf, Gauss.neg_zero]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [pneg, coeffOf, ih]
      by_cases h : m = t
      · rw [ite_eq_left h, ite_eq_left h, Gauss.neg_add]
      · rw [ite_eq_right h, ite_eq_right h]
        simp only [Gauss.zero_add]

theorem coeff_psub (p q : Poly) (t : Mono) :
    coeffOf (psub p q) t = coeffOf p t + -coeffOf q t := by
  rw [psub, coeffOf_append, coeff_pneg]

theorem coeff_scale (z : Gauss) (p : Poly) (t : Mono) :
    coeffOf (scale z p) t = z * coeffOf p t := by
  induction p with
  | nil => simp [scale, coeffOf, Gauss.mul_zero]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [scale, coeffOf, ih]
      by_cases h : m = t
      · rw [ite_eq_left h, ite_eq_left h, Gauss.mul_add]
      · rw [ite_eq_right h, ite_eq_right h]
        simp only [Gauss.zero_add]

theorem coeff_conj (p : Poly) (t : Mono) : coeffOf (conjP p) t = Gauss.conj (coeffOf p t) := by
  induction p with
  | nil => simp [conjP, coeffOf, conj_zero]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [conjP, coeffOf, ih]
      by_cases h : m = t
      · rw [ite_eq_left h, ite_eq_left h, conj_add]
      · rw [ite_eq_right h, ite_eq_right h, conj_add, conj_zero]

theorem coeff_single_eq (a : Gauss) (m t : Mono) :
    coeffOf (single a m) t = if m = t then a else 0 := by
  simp [single, coeffOf, Gauss.add_zero]

/-! ### Prodotto: uguaglianze di lista -/

theorem mulMono_append (a : Gauss) (m : Mono) (p q : Poly) :
    mulMono a m (p ++ q) = mulMono a m p ++ mulMono a m q := by
  induction p with
  | nil => simp [mulMono, List.nil_append]
  | cons head rest ih =>
    cases head with
    | mk b n => simp [mulMono, List.cons_append, ih]

theorem pmul_nil (p : Poly) : pmul p [] = [] := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m => simp [pmul, Universe.Quotient.mul, mulMono, ih]

theorem pmul_append_left (p q r : Poly) : pmul (p ++ q) r = pmul p r ++ pmul q r := by
  induction p with
  | nil => simp [pmul, Universe.Quotient.mul, List.nil_append]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, pmul, Universe.Quotient.mul, ih, List.append_assoc]

theorem mulMono_compose (a b : Gauss) (m n : Mono) (q : Poly) :
    mulMono (a * b) (m.mul n) q = mulMono a m (mulMono b n q) := by
  induction q with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk c k =>
      simp only [mulMono, ih]
      rw [Gauss.mul_assoc, Mono.mul_assoc]

theorem mulMono_pmul (a : Gauss) (m : Mono) (p q : Poly) :
    pmul (mulMono a m p) q = mulMono a m (pmul p q) := by
  induction p with
  | nil => simp [mulMono, pmul, Universe.Quotient.mul]
  | cons head rest ih =>
    cases head with
    | mk b n =>
      simp only [mulMono, pmul, Universe.Quotient.mul, ih, mulMono_append, mulMono_compose]

theorem pmul_assoc (p q r : Poly) : pmul (pmul p q) r = pmul p (pmul q r) := by
  induction p with
  | nil => simp [pmul, Universe.Quotient.mul]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [pmul, Universe.Quotient.mul, pmul_append_left, mulMono_pmul, ih]

theorem pmul_one (p : Poly) : pmul p (single 1 Mono.one) = p := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show pmul ((a, m) :: rest) (single 1 Mono.one) =
        (a * 1, m.mul Mono.one) :: pmul rest (single 1 Mono.one) from rfl]
      rw [ih, Gauss.mul_one, Mono.mul_one]

theorem one_pmul (p : Poly) : pmul (single 1 Mono.one) p = p := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      have hmul : mulMono (1 : Gauss) Mono.one rest = rest := by
        have h := ih
        rw [show pmul (single 1 Mono.one) rest = mulMono (1 : Gauss) Mono.one rest ++ [] from rfl] at h
        simpa [List.append_nil] using h
      rw [show pmul (single 1 Mono.one) ((a, m) :: rest) =
        ((1 * a, Mono.one.mul m) :: mulMono (1 : Gauss) Mono.one rest) ++ [] from rfl]
      rw [List.append_nil, Gauss.one_mul, Mono.one_mul, hmul]

theorem pmul_single_single (a b : Gauss) (m n : Mono) :
    pmul (single a m) (single b n) = single (a * b) (m.mul n) ++ [] := by
  simp [pmul, Universe.Quotient.mul, single, mulMono]

theorem scale_append (z : Gauss) (p q : Poly) : scale z (p ++ q) = scale z p ++ scale z q := by
  induction p with
  | nil => simp [scale, List.nil_append]
  | cons head rest ih =>
    cases head with
    | mk a m => simp [scale, List.cons_append, ih]

theorem scale_one (p : Poly) : scale (1 : Gauss) p = p := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m => simp [scale, ih, Gauss.one_mul]

theorem scale_mul_gauss (z w : Gauss) (p : Poly) : scale (z * w) p = scale z (scale w p) := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m => simp [scale, ih, Gauss.mul_assoc]

theorem scale_zero_coeff (p : Poly) (t : Mono) : coeffOf (scale (0 : Gauss) p) t = 0 := by
  rw [coeff_scale, Gauss.zero_mul]

theorem pneg_append (p q : Poly) : pneg (p ++ q) = pneg p ++ pneg q := by
  induction p with
  | nil => simp [pneg, List.nil_append]
  | cons head rest ih =>
    cases head with
    | mk a m => simp [pneg, List.cons_append, ih]

theorem pneg_mulMono (a : Gauss) (m : Mono) (q : Poly) :
    pneg (mulMono a m q) = mulMono (-a) m q := by
  induction q with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk b n => simp [mulMono, pneg, ih, Gauss.neg_mul]

theorem pneg_pmul (p q : Poly) : pneg (pmul p q) = pmul (pneg p) q := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [pneg, pmul, Universe.Quotient.mul, pneg_append, pneg_mulMono, ih]

theorem conj_append (p q : Poly) : conjP (p ++ q) = conjP p ++ conjP q := by
  induction p with
  | nil => simp [conjP, List.nil_append]
  | cons head rest ih =>
    cases head with
    | mk a m => simp [conjP, List.cons_append, ih]

theorem conj_mulMono (a : Gauss) (m : Mono) (q : Poly) :
    conjP (mulMono a m q) = mulMono (Gauss.conj a) m (conjP q) := by
  induction q with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk b n => simp [mulMono, conjP, ih, conj_mul]

theorem conj_pmul (p q : Poly) : conjP (pmul p q) = pmul (conjP p) (conjP q) := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [conjP, pmul, Universe.Quotient.mul, conj_append, conj_mulMono, ih]

theorem conj_pneg (p : Poly) : conjP (pneg p) = pneg (conjP p) := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m => simp [pneg, conjP, ih, conj_neg]

/-! ### Il prodotto dipende solo dai coefficienti -/

def support : Poly → List Mono
  | [] => []
  | (_, m) :: rest =>
    let s := support rest
    if m ∈ s then s else m :: s

theorem support_nodup (p : Poly) : (support p).Nodup := by
  induction p with
  | nil =>
    simp only [support]
    exact List.Pairwise.nil
  | cons head rest ih =>
    cases head with
    | mk _ m =>
      simp only [support]
      by_cases h : m ∈ support rest
      · rw [ite_eq_left h]
        exact ih
      · rw [ite_eq_right h, List.nodup_cons]
        exact ⟨h, ih⟩

theorem mem_support_cons (a : Gauss) (n : Mono) (rest : Poly) (m : Mono) :
    m ∈ support ((a, n) :: rest) ↔ m = n ∨ m ∈ support rest := by
  simp only [support]
  by_cases h : n ∈ support rest
  · rw [ite_eq_left h]
    constructor
    · intro hm
      exact Or.inr hm
    · intro hm
      cases hm with
      | inl heq =>
        subst heq
        exact h
      | inr hm => exact hm
  · rw [ite_eq_right h, List.mem_cons]

theorem mem_support_append (p q : Poly) (m : Mono) :
    m ∈ support (p ++ q) ↔ m ∈ support p ∨ m ∈ support q := by
  induction p with
  | nil =>
    simp only [List.nil_append, support]
    constructor
    · intro hm
      exact Or.inr hm
    · intro hm
      cases hm with
      | inl hm => cases hm
      | inr hm => exact hm
  | cons head rest ih =>
    cases head with
    | mk a n =>
      rw [List.cons_append, mem_support_cons, mem_support_cons, ih]
      constructor
      · intro hm
        cases hm with
        | inl hm => exact Or.inl (Or.inl hm)
        | inr hm =>
          cases hm with
          | inl hm => exact Or.inl (Or.inr hm)
          | inr hm => exact Or.inr hm
      · intro hm
        cases hm with
        | inl hm =>
          cases hm with
          | inl hm => exact Or.inl hm
          | inr hm => exact Or.inr (Or.inl hm)
        | inr hm => exact Or.inr (Or.inr hm)

theorem not_support_coeff (p : Poly) (m : Mono) (h : m ∉ support p) : coeffOf p m = 0 := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a n =>
      rw [mem_support_cons] at h
      simp only [coeffOf]
      by_cases hn : m = n
      · exact absurd (Or.inl hn) h
      · rw [ite_eq_right (Ne.symm hn), Gauss.zero_add]
        exact ih (fun hm => h (Or.inr hm))

/-- Somma `Σ_m coeff(p, m) · coeff(q, t / m)` lungo una lista di monomi. -/
def listContrib (p q : Poly) (t : Mono) : List Mono → Gauss
  | [] => 0
  | m :: ms => factor (coeffOf p m) m q t + listContrib p q t ms

theorem factor_add (x y : Gauss) (m : Mono) (q : Poly) (t : Mono) :
    factor (x + y) m q t = factor x m q t + factor y m q t := by
  cases hsub : subExp t m with
  | none => simp only [factor, hsub, Gauss.add_zero]
  | some k =>
    simp only [factor, hsub]
    rw [Gauss.add_mul]

theorem factor_zero (m : Mono) (q : Poly) (t : Mono) : factor (0 : Gauss) m q t = 0 := by
  cases hsub : subExp t m with
  | none => simp only [factor, hsub]
  | some k => simp only [factor, hsub, Gauss.zero_mul]

theorem listContrib_zero_poly (q : Poly) (t : Mono) (ms : List Mono) :
    listContrib [] q t ms = 0 := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [listContrib, coeffOf, factor_zero, Gauss.zero_add, ih]

theorem listContrib_coeff {p p' q : Poly} {t : Mono} {ms : List Mono}
    (h : ∀ m, m ∈ ms → coeffOf p m = coeffOf p' m) :
    listContrib p q t ms = listContrib p' q t ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [listContrib, h m List.mem_cons_self]
    rw [ih (fun n hn => h n (List.mem_cons_of_mem m hn))]

theorem listContrib_cons_poly (a : Gauss) (mono : Mono) (rest q : Poly) (t : Mono)
    (ms : List Mono) (hnd : ms.Nodup) (hm : mono ∈ ms) :
    listContrib ((a, mono) :: rest) q t ms =
      factor a mono q t + listContrib rest q t ms := by
  induction ms with
  | nil => cases hm
  | cons n ns ih =>
    rw [List.nodup_cons] at hnd
    simp only [listContrib]
    by_cases hn : n = mono
    · subst hn
      have htail : listContrib ((a, n) :: rest) q t ns = listContrib rest q t ns := by
        apply listContrib_coeff
        intro n' hn'
        have hne : n ≠ n' := fun he => hnd.1 (he ▸ hn')
        simp only [coeffOf, ite_eq_right hne, Gauss.zero_add]
      rw [htail]
      have hc : coeffOf ((a, n) :: rest) n = a + coeffOf rest n := by
        simp only [coeffOf, ite_true]
      rw [hc, factor_add, Gauss.add_assoc]
    · have hm' : mono ∈ ns := by
        cases hm with
        | head => exact absurd rfl hn
        | tail _ hmem => exact hmem
      have hc : coeffOf ((a, mono) :: rest) n = coeffOf rest n := by
        simp only [coeffOf, ite_eq_right (Ne.symm hn), Gauss.zero_add]
      rw [hc, ih hnd.2 hm']
      rw [← Gauss.add_assoc, Gauss.add_comm (factor (coeffOf rest n) n q t), Gauss.add_assoc]

theorem coeff_eq_listContrib (q : Poly) (t : Mono) (p : Poly) :
    ∀ ms, ms.Nodup → (∀ m, m ∈ support p → m ∈ ms) →
      coeffOf (pmul p q) t = listContrib p q t ms := by
  induction p with
  | nil =>
    intro ms _ _
    simp only [pmul, Universe.Quotient.mul, coeffOf]
    exact (listContrib_zero_poly q t ms).symm
  | cons head rest ih =>
    cases head with
    | mk a mono =>
      intro ms hnd hcover
      have hmono : mono ∈ ms :=
        hcover mono ((mem_support_cons a mono rest mono).2 (Or.inl rfl))
      have hcoverRest : ∀ m, m ∈ support rest → m ∈ ms := by
        intro m hm
        exact hcover m ((mem_support_cons a mono rest m).2 (Or.inr hm))
      rw [show pmul ((a, mono) :: rest) q = mulMono a mono q ++ pmul rest q from rfl]
      rw [coeffOf_append, coeffOf_mulMono, ih ms hnd hcoverRest]
      exact (listContrib_cons_poly a mono rest q t ms hnd hmono).symm

theorem coeff_mul_congr_left {p p' : Poly} (h : ∀ u, coeffOf p u = coeffOf p' u)
    (q : Poly) (t : Mono) : coeffOf (pmul p q) t = coeffOf (pmul p' q) t := by
  let ms := support (p ++ p')
  have hnd : ms.Nodup := support_nodup (p ++ p')
  have hcov : ∀ m, m ∈ support p → m ∈ ms := fun m hm =>
    (mem_support_append p p' m).2 (Or.inl hm)
  have hcov' : ∀ m, m ∈ support p' → m ∈ ms := fun m hm =>
    (mem_support_append p p' m).2 (Or.inr hm)
  rw [coeff_eq_listContrib q t p ms hnd hcov, coeff_eq_listContrib q t p' ms hnd hcov']
  exact listContrib_coeff (fun m _ => h m)

theorem coeff_single_right (q : Poly) (a : Gauss) (m t : Mono) :
    coeffOf (pmul q (single a m)) t = coeffOf (mulMono a m q) t := by
  induction q with
  | nil => simp [pmul, Universe.Quotient.mul, mulMono, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk b n =>
      rw [show pmul ((b, n) :: rest) (single a m) =
        mulMono b n (single a m) ++ pmul rest (single a m) from rfl]
      rw [coeffOf_append, ih]
      have hsingle : mulMono b n (single a m) = single (b * a) (n.mul m) := by
        simp [mulMono, single]
      rw [hsingle, coeff_single_eq]
      rw [show mulMono a m ((b, n) :: rest) = (a * b, m.mul n) :: mulMono a m rest from rfl]
      simp only [coeffOf]
      rw [Gauss.mul_comm b a, Mono.mul_comm n m]

theorem coeff_mul_append_right (p q r : Poly) (t : Mono) :
    coeffOf (pmul p (q ++ r)) t = coeffOf (pmul p q ++ pmul p r) t := by
  induction p with
  | nil => simp [pmul, Universe.Quotient.mul, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [pmul, Universe.Quotient.mul, mulMono_append, coeffOf_append, ih]
      rw [Gauss.add_add_add_comm]

theorem coeff_mul_comm (p q : Poly) (t : Mono) :
    coeffOf (pmul p q) t = coeffOf (pmul q p) t := by
  induction p with
  | nil => simp [pmul, Universe.Quotient.mul, pmul_nil, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show pmul ((a, m) :: rest) q = mulMono a m q ++ pmul rest q from rfl]
      rw [coeffOf_append, ← coeff_single_right, ih, ← coeffOf_append, ← coeff_mul_append_right]
      rfl

theorem coeff_mul_congr_right {q q' : Poly} (h : ∀ u, coeffOf q u = coeffOf q' u)
    (p : Poly) (t : Mono) : coeffOf (pmul p q) t = coeffOf (pmul p q') t := by
  rw [coeff_mul_comm p q, coeff_mul_comm p q']
  exact coeff_mul_congr_left h p t

theorem polySame_pmul_left {p p' : Poly} (h : polySame p p') (q : Poly) :
    polySame (pmul p q) (pmul p' q) :=
  fun t => coeff_mul_congr_left h q t

theorem polySame_pmul_right {q q' : Poly} (h : polySame q q') (p : Poly) :
    polySame (pmul p q) (pmul p q') :=
  fun t => coeff_mul_congr_right h p t

/-! ### Ideale dei due quadrati -/

def inIdeal (p : Poly) : Prop :=
  ∃ fc fn, ∀ t, coeffOf p t = coeffOf (pmul fc gC ++ pmul fn gN) t

theorem inIdeal_of_polySame {p q : Poly} (h : polySame p q) : inIdeal (psub p q) := by
  refine ⟨[], [], ?_⟩
  intro t
  rw [coeff_psub, h t, Gauss.add_neg_cancel]
  simp [pmul, Universe.Quotient.mul, coeffOf_nil]

theorem inIdeal_zero : inIdeal [] := by
  refine ⟨[], [], ?_⟩
  intro t
  simp [pmul, Universe.Quotient.mul, coeffOf_nil]

theorem inIdeal_gC : inIdeal gC := by
  refine ⟨single 1 Mono.one, [], ?_⟩
  intro t
  rw [one_pmul, show pmul [] gN = [] from rfl, List.append_nil]

theorem inIdeal_gN : inIdeal gN := by
  refine ⟨[], single 1 Mono.one, ?_⟩
  intro t
  rw [one_pmul]
  rfl

theorem inIdeal_append {p q : Poly} (hp : inIdeal p) (hq : inIdeal q) : inIdeal (p ++ q) := by
  rcases hp with ⟨fc, fn, hp⟩
  rcases hq with ⟨gc, gn, hq⟩
  refine ⟨fc ++ gc, fn ++ gn, ?_⟩
  intro t
  have hL : coeffOf (p ++ q) t =
      coeffOf (pmul fc gC) t + coeffOf (pmul fn gN) t +
        (coeffOf (pmul gc gC) t + coeffOf (pmul gn gN) t) := by
    rw [coeffOf_append, hp, hq, coeffOf_append, coeffOf_append]
  have hR : coeffOf (pmul (fc ++ gc) gC ++ pmul (fn ++ gn) gN) t =
      coeffOf (pmul fc gC) t + coeffOf (pmul gc gC) t +
        (coeffOf (pmul fn gN) t + coeffOf (pmul gn gN) t) := by
    rw [pmul_append_left, pmul_append_left, coeffOf_append, coeffOf_append, coeffOf_append]
  rw [hL, hR]
  exact Gauss.add_add_add_comm _ _ _ _

theorem inIdeal_neg {p : Poly} (hp : inIdeal p) : inIdeal (pneg p) := by
  rcases hp with ⟨fc, fn, hp⟩
  refine ⟨pneg fc, pneg fn, ?_⟩
  intro t
  rw [coeff_pneg, hp, coeffOf_append, Gauss.neg_add, ← coeff_pneg, ← coeff_pneg,
    pneg_pmul, pneg_pmul, coeffOf_append]

theorem inIdeal_psub {p q : Poly} (hp : inIdeal p) (hq : inIdeal q) : inIdeal (psub p q) :=
  inIdeal_append hp (inIdeal_neg hq)

theorem scale_mulMono (z a : Gauss) (m : Mono) (q : Poly) :
    scale z (mulMono a m q) = mulMono (z * a) m q := by
  induction q with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk b n => simp [mulMono, scale, ih, Gauss.mul_assoc]

theorem scale_pmul_left (z : Gauss) (p q : Poly) :
    scale z (pmul p q) = pmul (scale z p) q := by
  induction p with
  | nil => simp [scale, pmul, Universe.Quotient.mul]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [scale, pmul, Universe.Quotient.mul, scale_append, scale_mulMono, ih]

theorem inIdeal_scale {p : Poly} (z : Gauss) (hp : inIdeal p) : inIdeal (scale z p) := by
  rcases hp with ⟨fc, fn, hp⟩
  refine ⟨scale z fc, scale z fn, ?_⟩
  intro t
  rw [coeff_scale, hp, coeffOf_append, Gauss.mul_add, ← coeff_scale, ← coeff_scale,
    scale_pmul_left, scale_pmul_left, coeffOf_append]

theorem inIdeal_mul_right {p : Poly} (q : Poly) (hp : inIdeal p) : inIdeal (pmul p q) := by
  rcases hp with ⟨fc, fn, hp⟩
  refine ⟨pmul fc q, pmul fn q, ?_⟩
  intro t
  rw [coeff_mul_congr_left hp]
  rw [pmul_append_left, coeffOf_append, pmul_assoc, pmul_assoc]
  rw [coeff_mul_congr_right (fun u => coeff_mul_comm gC q u),
    coeff_mul_congr_right (fun u => coeff_mul_comm gN q u)]
  rw [← pmul_assoc, ← pmul_assoc, coeffOf_append]

theorem inIdeal_mul_left {p : Poly} (q : Poly) (hp : inIdeal p) : inIdeal (pmul q p) := by
  rcases hp with ⟨fc, fn, hp⟩
  refine ⟨pmul q fc, pmul q fn, ?_⟩
  intro t
  rw [coeff_mul_congr_right hp, coeff_mul_append_right, ← pmul_assoc, ← pmul_assoc, coeffOf_append]

theorem inIdeal_polySame {p q : Poly} (h : polySame p q) (hq : inIdeal q) : inIdeal p := by
  rcases hq with ⟨fc, fn, hq⟩
  exact ⟨fc, fn, fun t => (h t).trans (hq t)⟩

theorem polySame_refl (p : Poly) : polySame p p := fun _ => rfl

theorem polySame.symm {p q : Poly} (h : polySame p q) : polySame q p :=
  fun t => (h t).symm

theorem polySame.trans {p q r : Poly} (hpq : polySame p q) (hqr : polySame q r) : polySame p r :=
  fun t => (hpq t).trans (hqr t)

theorem polySame_append {p p' q q' : Poly} (hp : polySame p p') (hq : polySame q q') :
    polySame (p ++ q) (p' ++ q') := by
  intro t
  rw [coeffOf_append, coeffOf_append, hp t, hq t]

theorem polySame_pneg {p q : Poly} (h : polySame p q) : polySame (pneg p) (pneg q) := by
  intro t
  rw [coeff_pneg, coeff_pneg, h t]

theorem coeff_pmul_pneg_right (p q : Poly) (t : Mono) :
    coeffOf (pmul p (pneg q)) t = -coeffOf (pmul p q) t := by
  rw [coeff_mul_comm, ← pneg_pmul, coeff_pneg, coeff_mul_comm]

theorem polySame_mul_psub_right (a c c' : Poly) :
    polySame (pmul a (psub c c')) (psub (pmul a c) (pmul a c')) := by
  intro t
  rw [coeff_psub, psub, coeff_mul_append_right, coeffOf_append, coeff_pmul_pneg_right]

theorem polySame_mul_psub_left (a a' c : Poly) :
    polySame (pmul (psub a a') c) (psub (pmul a c) (pmul a' c)) := by
  intro t
  rw [coeff_psub, psub, pmul_append_left, ← pneg_pmul, coeffOf_append, coeff_pneg]

theorem Gauss.sub_trans (a b c : Gauss) : a + -c = (a + -b) + (b + -c) := by
  ext <;> simp <;> grind

theorem polySame_psub_trans (p q r : Poly) :
    polySame (psub p r) (psub p q ++ psub q r) := by
  intro t
  rw [coeff_psub, coeffOf_append, coeff_psub, coeff_psub, Gauss.sub_trans]

theorem polySame_psub_append (a b a' b' : Poly) :
    polySame (psub (a ++ b) (a' ++ b')) (psub a a' ++ psub b b') := by
  intro t
  calc
    coeffOf (psub (a ++ b) (a' ++ b')) t
        = coeffOf (a ++ b) t + -coeffOf (a' ++ b') t := by rw [coeff_psub]
    _ = (coeffOf a t + coeffOf b t) + -(coeffOf a' t + coeffOf b' t) := by
          rw [coeffOf_append, coeffOf_append]
    _ = (coeffOf a t + coeffOf b t) + (-coeffOf a' t + -coeffOf b' t) := by
          rw [Gauss.neg_add]
    _ = (coeffOf a t + -coeffOf a' t) + (coeffOf b t + -coeffOf b' t) :=
          Gauss.add_add_add_comm _ _ _ _
    _ = coeffOf (psub a a') t + coeffOf (psub b b') t := by
          rw [← coeff_psub, ← coeff_psub]
    _ = coeffOf (psub a a' ++ psub b b') t := by rw [← coeffOf_append]

theorem polySame_dot_sub_right (a b c c' d d' : Poly) :
    polySame (psub (pmul a c ++ pmul b d) (pmul a c' ++ pmul b d'))
      (pmul a (psub c c') ++ pmul b (psub d d')) :=
  polySame.trans (polySame_psub_append _ _ _ _)
    (polySame_append (polySame.symm (polySame_mul_psub_right a c c'))
      (polySame.symm (polySame_mul_psub_right b d d')))

theorem polySame_dot_sub_left (a a' b b' c d : Poly) :
    polySame (psub (pmul a c ++ pmul b d) (pmul a' c ++ pmul b' d))
      (pmul (psub a a') c ++ pmul (psub b b') d) :=
  polySame.trans (polySame_psub_append _ _ _ _)
    (polySame_append (polySame.symm (polySame_mul_psub_left a a' c))
      (polySame.symm (polySame_mul_psub_left b b' d)))

theorem inIdeal_dot_right (a b c c' d d' : Poly) (hc : inIdeal (psub c c'))
    (hd : inIdeal (psub d d')) :
    inIdeal (psub (pmul a c ++ pmul b d) (pmul a c' ++ pmul b d')) :=
  inIdeal_polySame (polySame_dot_sub_right a b c c' d d')
    (inIdeal_append (inIdeal_mul_left a hc) (inIdeal_mul_left b hd))

theorem inIdeal_dot_left (a a' b b' c d : Poly) (ha : inIdeal (psub a a'))
    (hb : inIdeal (psub b b')) :
    inIdeal (psub (pmul a c ++ pmul b d) (pmul a' c ++ pmul b' d)) :=
  inIdeal_polySame (polySame_dot_sub_left a a' b b' c d)
    (inIdeal_append (inIdeal_mul_right c ha) (inIdeal_mul_right d hb))

theorem polySame_pmul_assoc (a b c : Poly) :
    polySame (pmul (pmul a b) c) (pmul a (pmul b c)) := by
  intro t
  rw [pmul_assoc]

theorem polySame_append4_mid (a b c d : Poly) :
    polySame ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d)) := by
  intro t
  rw [coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append, coeffOf_append,
    coeffOf_append]
  exact Gauss.add_add_add_comm _ _ _ _

/-! ### Matrici 2×2 -/

@[ext]
structure Mat where
  a00 : Poly
  a01 : Poly
  a10 : Poly
  a11 : Poly

def matZero : Mat := ⟨[], [], [], []⟩

def matOne : Mat := ⟨single 1 Mono.one, [], [], single 1 Mono.one⟩

def matAdd (M N : Mat) : Mat :=
  ⟨M.a00 ++ N.a00, M.a01 ++ N.a01, M.a10 ++ N.a10, M.a11 ++ N.a11⟩

def matNeg (M : Mat) : Mat := ⟨pneg M.a00, pneg M.a01, pneg M.a10, pneg M.a11⟩

def matSmul (z : Gauss) (M : Mat) : Mat :=
  ⟨scale z M.a00, scale z M.a01, scale z M.a10, scale z M.a11⟩

def matScale (p : Poly) (M : Mat) : Mat :=
  ⟨pmul p M.a00, pmul p M.a01, pmul p M.a10, pmul p M.a11⟩

def matMul (M N : Mat) : Mat where
  a00 := pmul M.a00 N.a00 ++ pmul M.a01 N.a10
  a01 := pmul M.a00 N.a01 ++ pmul M.a01 N.a11
  a10 := pmul M.a10 N.a00 ++ pmul M.a11 N.a10
  a11 := pmul M.a10 N.a01 ++ pmul M.a11 N.a11

def matDagger (M : Mat) : Mat :=
  ⟨conjP M.a00, conjP M.a10, conjP M.a01, conjP M.a11⟩

def matSame (M N : Mat) : Prop :=
  polySame M.a00 N.a00 ∧ polySame M.a01 N.a01 ∧ polySame M.a10 N.a10 ∧ polySame M.a11 N.a11

def matRel (M N : Mat) : Prop :=
  inIdeal (psub M.a00 N.a00) ∧ inIdeal (psub M.a01 N.a01) ∧
    inIdeal (psub M.a10 N.a10) ∧ inIdeal (psub M.a11 N.a11)

theorem matSame_refl (M : Mat) : matSame M M :=
  ⟨polySame_refl _, polySame_refl _, polySame_refl _, polySame_refl _⟩

theorem matRel_of_matSame {M N : Mat} (h : matSame M N) : matRel M N :=
  ⟨inIdeal_of_polySame h.1, inIdeal_of_polySame h.2.1, inIdeal_of_polySame h.2.2.1,
    inIdeal_of_polySame h.2.2.2⟩

theorem matRel_refl (M : Mat) : matRel M M :=
  matRel_of_matSame (matSame_refl M)

theorem matRel_symm {M N : Mat} (h : matRel M N) : matRel N M := by
  have swap (p q : Poly) (hp : inIdeal (psub p q)) : inIdeal (psub q p) := by
    have hs : polySame (psub q p) (pneg (psub p q)) := by
      intro t
      rw [coeff_psub, coeff_pneg, coeff_psub, Gauss.neg_add, Gauss.neg_neg, Gauss.add_comm]
    exact inIdeal_polySame hs (inIdeal_neg hp)
  exact ⟨swap _ _ h.1, swap _ _ h.2.1, swap _ _ h.2.2.1, swap _ _ h.2.2.2⟩

theorem matRel_trans {M N P : Mat} (hMN : matRel M N) (hNP : matRel N P) : matRel M P := by
  have step (a b c : Poly) (hab : inIdeal (psub a b)) (hbc : inIdeal (psub b c)) :
      inIdeal (psub a c) :=
    inIdeal_polySame (polySame_psub_trans a b c) (inIdeal_append hab hbc)
  exact ⟨step _ _ _ hMN.1 hNP.1, step _ _ _ hMN.2.1 hNP.2.1, step _ _ _ hMN.2.2.1 hNP.2.2.1,
    step _ _ _ hMN.2.2.2 hNP.2.2.2⟩

instance matSetoid : Setoid Mat where
  r := matRel
  iseqv := ⟨matRel_refl, fun h => matRel_symm h, fun h1 h2 => matRel_trans h1 h2⟩

abbrev QMat := Quotient matSetoid

theorem matAdd_rel {M M' N N' : Mat} (hM : matRel M M') (hN : matRel N N') :
    matRel (matAdd M N) (matAdd M' N') := by
  have entry (a b a' b' : Poly) (ha : inIdeal (psub a a')) (hb : inIdeal (psub b b')) :
      inIdeal (psub (a ++ b) (a' ++ b')) :=
    inIdeal_polySame (polySame_psub_append a b a' b') (inIdeal_append ha hb)
  exact ⟨entry _ _ _ _ hM.1 hN.1, entry _ _ _ _ hM.2.1 hN.2.1, entry _ _ _ _ hM.2.2.1 hN.2.2.1,
    entry _ _ _ _ hM.2.2.2 hN.2.2.2⟩

theorem matMul_right_rel (M : Mat) {N N' : Mat} (h : matRel N N') :
    matRel (matMul M N) (matMul M N') := by
  exact ⟨inIdeal_dot_right _ _ _ _ _ _ h.1 h.2.2.1, inIdeal_dot_right _ _ _ _ _ _ h.2.1 h.2.2.2,
    inIdeal_dot_right _ _ _ _ _ _ h.1 h.2.2.1, inIdeal_dot_right _ _ _ _ _ _ h.2.1 h.2.2.2⟩

theorem matMul_left_rel {M M' : Mat} (h : matRel M M') (N : Mat) :
    matRel (matMul M N) (matMul M' N) := by
  exact ⟨inIdeal_dot_left _ _ _ _ _ _ h.1 h.2.1, inIdeal_dot_left _ _ _ _ _ _ h.1 h.2.1,
    inIdeal_dot_left _ _ _ _ _ _ h.2.2.1 h.2.2.2, inIdeal_dot_left _ _ _ _ _ _ h.2.2.1 h.2.2.2⟩

theorem matSmul_rel (z : Gauss) {M N : Mat} (h : matRel M N) :
    matRel (matSmul z M) (matSmul z N) := by
  have entry (p q : Poly) (hp : inIdeal (psub p q)) : inIdeal (psub (scale z p) (scale z q)) := by
    have hs : polySame (psub (scale z p) (scale z q)) (scale z (psub p q)) := by
      intro t
      rw [coeff_psub, coeff_scale, coeff_scale, coeff_scale, coeff_psub, Gauss.mul_add, Gauss.mul_neg]
    exact inIdeal_polySame hs (inIdeal_scale z hp)
  exact ⟨entry _ _ h.1, entry _ _ h.2.1, entry _ _ h.2.2.1, entry _ _ h.2.2.2⟩

noncomputable def qmul (x y : QMat) : QMat :=
  Quot.lift
    (fun M : Mat =>
      Quot.lift (fun N : Mat => Quotient.mk matSetoid (matMul M N))
        (fun _ _ h => Quotient.sound (matMul_right_rel M h)) y)
    (fun M M' h => by
      induction y using Quotient.ind with
      | _ N =>
        apply Quotient.sound
        exact matMul_left_rel h N)
    x

noncomputable def qadd (x y : QMat) : QMat :=
  Quotient.lift₂ (fun M N => Quotient.mk matSetoid (matAdd M N))
    (fun _ _ _ _ hM hN => Quotient.sound (matAdd_rel hM hN)) x y

noncomputable def qsmul (z : Gauss) (x : QMat) : QMat :=
  Quotient.lift (fun M => Quotient.mk matSetoid (matSmul z M))
    (fun _ _ h => Quotient.sound (matSmul_rel z h)) x

theorem qmul_mk (M N : Mat) :
    qmul (Quotient.mk matSetoid M) (Quotient.mk matSetoid N) =
      Quotient.mk matSetoid (matMul M N) :=
  rfl

theorem qadd_mk (M N : Mat) :
    qadd (Quotient.mk matSetoid M) (Quotient.mk matSetoid N) =
      Quotient.mk matSetoid (matAdd M N) :=
  rfl

theorem qsmul_mk (z : Gauss) (M : Mat) :
    qsmul z (Quotient.mk matSetoid M) = Quotient.mk matSetoid (matSmul z M) :=
  rfl

theorem matMul_one_left (M : Mat) : matMul matOne M = M := by
  apply Mat.ext
  · show pmul (single 1 Mono.one) M.a00 ++ pmul [] M.a10 = M.a00
    rw [one_pmul, show pmul [] M.a10 = [] from rfl, List.append_nil]
  · show pmul (single 1 Mono.one) M.a01 ++ pmul [] M.a11 = M.a01
    rw [one_pmul, show pmul [] M.a11 = [] from rfl, List.append_nil]
  · show pmul [] M.a00 ++ pmul (single 1 Mono.one) M.a10 = M.a10
    rw [show pmul [] M.a00 = [] from rfl, one_pmul, List.nil_append]
  · show pmul [] M.a01 ++ pmul (single 1 Mono.one) M.a11 = M.a11
    rw [show pmul [] M.a01 = [] from rfl, one_pmul, List.nil_append]

theorem matMul_one_right (M : Mat) : matMul M matOne = M := by
  cases M
  simp [matMul, matOne, pmul_one, pmul_nil, List.append_nil]

theorem matAdd_zero (M : Mat) : matAdd M matZero = M := by
  cases M
  simp [matAdd, matZero, List.append_nil]

theorem matZero_add (M : Mat) : matAdd matZero M = M := by
  cases M
  rfl

theorem matSmul_one (M : Mat) : matSmul 1 M = M := by
  cases M
  simp [matSmul, scale_one]

theorem matSmul_mul_gauss (z w : Gauss) (M : Mat) :
    matSmul (z * w) M = matSmul z (matSmul w M) := by
  cases M
  simp [matSmul, scale_mul_gauss]

theorem matSmul_add (z : Gauss) (M N : Mat) :
    matSmul z (matAdd M N) = matAdd (matSmul z M) (matSmul z N) := by
  cases M
  cases N
  simp [matSmul, matAdd, scale_append]

theorem matZero_smul_rel (M : Mat) : matRel (matSmul 0 M) matZero := by
  have entry (p : Poly) : inIdeal (psub (scale 0 p) []) := by
    refine inIdeal_of_polySame ?_
    intro t
    rw [coeff_scale, Gauss.zero_mul, coeffOf_nil]
  exact ⟨entry _, entry _, entry _, entry _⟩

theorem matMul_zero_left (M : Mat) : matMul matZero M = matZero := by
  cases M
  simp [matMul, matZero, pmul, Universe.Quotient.mul]

theorem matMul_zero_right (M : Mat) : matMul M matZero = matZero := by
  cases M
  simp [matMul, matZero, pmul_nil]

theorem matSame_mul_assoc (M N P : Mat) :
    matSame (matMul (matMul M N) P) (matMul M (matMul N P)) := by
  have entry (a c e g f h b d : Poly) :
      polySame (pmul (pmul a e ++ pmul c g) b ++ pmul (pmul a f ++ pmul c h) d)
        (pmul a (pmul e b ++ pmul f d) ++ pmul c (pmul g b ++ pmul h d)) := by
    intro t
    calc
      coeffOf (pmul (pmul a e ++ pmul c g) b ++ pmul (pmul a f ++ pmul c h) d) t
          = coeffOf (pmul (pmul a e ++ pmul c g) b) t +
              coeffOf (pmul (pmul a f ++ pmul c h) d) t := by rw [coeffOf_append]
      _ = coeffOf (pmul (pmul a e) b ++ pmul (pmul c g) b) t +
            coeffOf (pmul (pmul a f) d ++ pmul (pmul c h) d) t := by
            rw [pmul_append_left, pmul_append_left]
      _ = (coeffOf (pmul (pmul a e) b) t + coeffOf (pmul (pmul c g) b) t) +
            (coeffOf (pmul (pmul a f) d) t + coeffOf (pmul (pmul c h) d) t) := by
            rw [coeffOf_append, coeffOf_append]
      _ = (coeffOf (pmul a (pmul e b)) t + coeffOf (pmul c (pmul g b)) t) +
            (coeffOf (pmul a (pmul f d)) t + coeffOf (pmul c (pmul h d)) t) := by
            rw [pmul_assoc, pmul_assoc, pmul_assoc, pmul_assoc]
      _ = (coeffOf (pmul a (pmul e b)) t + coeffOf (pmul a (pmul f d)) t) +
            (coeffOf (pmul c (pmul g b)) t + coeffOf (pmul c (pmul h d)) t) :=
            Gauss.add_add_add_comm _ _ _ _
      _ = coeffOf (pmul a (pmul e b) ++ pmul a (pmul f d)) t +
            coeffOf (pmul c (pmul g b) ++ pmul c (pmul h d)) t := by
            rw [← coeffOf_append, ← coeffOf_append]
      _ = coeffOf (pmul a (pmul e b ++ pmul f d)) t +
            coeffOf (pmul c (pmul g b ++ pmul h d)) t := by
            rw [← coeff_mul_append_right, ← coeff_mul_append_right]
      _ = coeffOf (pmul a (pmul e b ++ pmul f d) ++ pmul c (pmul g b ++ pmul h d)) t := by
            rw [← coeffOf_append]
  exact ⟨entry M.a00 M.a01 N.a00 N.a10 N.a01 N.a11 P.a00 P.a10,
    entry M.a00 M.a01 N.a00 N.a10 N.a01 N.a11 P.a01 P.a11,
    entry M.a10 M.a11 N.a00 N.a10 N.a01 N.a11 P.a00 P.a10,
    entry M.a10 M.a11 N.a00 N.a10 N.a01 N.a11 P.a01 P.a11⟩

noncomputable def qubitDyn : Dyn QMat where
  mul := qmul
  add := qadd
  one := Quotient.mk matSetoid matOne
  zero := Quotient.mk matSetoid matZero
  smul := qsmul
  mul_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro M N P
    rw [qmul_mk, qmul_mk, qmul_mk, qmul_mk]
    exact Quotient.sound (matRel_of_matSame (matSame_mul_assoc M N P))
  one_mul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro M
    rw [qmul_mk, matMul_one_left]
  mul_one := by
    intro x
    refine Quotient.inductionOn x ?_
    intro M
    rw [qmul_mk, matMul_one_right]
  add_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro M
    rw [qadd_mk, matAdd_zero]
  zero_add := by
    intro x
    refine Quotient.inductionOn x ?_
    intro M
    rw [qadd_mk, matZero_add]
  smul_one := by
    intro x
    refine Quotient.inductionOn x ?_
    intro M
    rw [qsmul_mk, matSmul_one]
  zero_smul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro M
    rw [qsmul_mk]
    exact Quotient.sound (matZero_smul_rel M)
  smul_mul := by
    intro z w x
    refine Quotient.inductionOn x ?_
    intro M
    rw [qsmul_mk, qsmul_mk, qsmul_mk, matSmul_mul_gauss]
  smul_add := by
    intro z x y
    refine Quotient.inductionOn₂ x y ?_
    intro M N
    rw [qadd_mk, qsmul_mk, qsmul_mk, qsmul_mk, qadd_mk, matSmul_add]

end Universe.Dynamics
