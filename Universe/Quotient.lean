/-
Quoziente a due quadrati, con cofattori.

Un polinomio è una lista di termini
`coefficiente · c^c s^s nx^nx ny^ny nz^nz ar^ar ai^ai br^br bi^bi`.
`reduce` sbuccia solo `c²` e `nx²`. `gA` è il terzo generatore, la sfera delle
ampiezze, e non entra in `reduce`.
- `c² = (1 − s²) + (c² + s² − 1)`
- `nx² = (1 − ny² − nz²) + (nx² + ny² + nz² − 1)`

`reduce` restituisce `resto`, `f`, `g`. Il teorema `reduce_sound` dice che, per ogni
polinomio e ogni monomio, i coefficienti coincidono:

`p = resto + f · (c² + s² − 1) + g · (nx² + ny² + nz² − 1)`.

Se il resto ha tutti i coefficienti zero, `p` sta nell'ideale.
-/
import Universe.Ring

namespace Universe.Quotient

open Universe.Ring

@[ext]
structure Mono where
  c : Nat
  s : Nat
  nx : Nat
  ny : Nat
  nz : Nat
  ar : Nat
  ai : Nat
  br : Nat
  bi : Nat
  deriving DecidableEq, Repr

namespace Mono

def one : Mono := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def mul (m n : Mono) : Mono where
  c := m.c + n.c
  s := m.s + n.s
  nx := m.nx + n.nx
  ny := m.ny + n.ny
  nz := m.nz + n.nz
  ar := m.ar + n.ar
  ai := m.ai + n.ai
  br := m.br + n.br
  bi := m.bi + n.bi

end Mono

def subExp (t m : Mono) : Option Mono :=
  if _h : m.c ≤ t.c ∧ m.s ≤ t.s ∧ m.nx ≤ t.nx ∧ m.ny ≤ t.ny ∧ m.nz ≤ t.nz ∧
      m.ar ≤ t.ar ∧ m.ai ≤ t.ai ∧ m.br ≤ t.br ∧ m.bi ≤ t.bi then
    some ⟨t.c - m.c, t.s - m.s, t.nx - m.nx, t.ny - m.ny, t.nz - m.nz,
      t.ar - m.ar, t.ai - m.ai, t.br - m.br, t.bi - m.bi⟩
  else
    none

theorem subExp_mul (m n : Mono) : subExp (m.mul n) m = some n := by
  have hc : m.c ≤ m.c + n.c := Nat.le_add_right _ _
  have hs : m.s ≤ m.s + n.s := Nat.le_add_right _ _
  have hnx : m.nx ≤ m.nx + n.nx := Nat.le_add_right _ _
  have hny : m.ny ≤ m.ny + n.ny := Nat.le_add_right _ _
  have hnz : m.nz ≤ m.nz + n.nz := Nat.le_add_right _ _
  have har : m.ar ≤ m.ar + n.ar := Nat.le_add_right _ _
  have hai : m.ai ≤ m.ai + n.ai := Nat.le_add_right _ _
  have hbr : m.br ≤ m.br + n.br := Nat.le_add_right _ _
  have hbi : m.bi ≤ m.bi + n.bi := Nat.le_add_right _ _
  unfold subExp
  rw [dite_eq_left ⟨hc, hs, hnx, hny, hnz, har, hai, hbr, hbi⟩]
  apply congrArg some
  ext <;> simp [Mono.mul, Nat.add_sub_cancel_left]

theorem mul_subExp {t m k : Mono} (h : subExp t m = some k) : m.mul k = t := by
  unfold subExp at h
  split at h
  · rename_i hle
    cases h
    ext
    · exact Nat.add_sub_of_le hle.1
    · exact Nat.add_sub_of_le hle.2.1
    · exact Nat.add_sub_of_le hle.2.2.1
    · exact Nat.add_sub_of_le hle.2.2.2.1
    · exact Nat.add_sub_of_le hle.2.2.2.2.1
    · exact Nat.add_sub_of_le hle.2.2.2.2.2.1
    · exact Nat.add_sub_of_le hle.2.2.2.2.2.2.1
    · exact Nat.add_sub_of_le hle.2.2.2.2.2.2.2.1
    · exact Nat.add_sub_of_le hle.2.2.2.2.2.2.2.2
  · cases h

abbrev Poly := List (Gauss × Mono)

def coeffOf : Poly → Mono → Gauss
  | [], _ => 0
  | (a, e) :: rest, m => (if e = m then a else 0) + coeffOf rest m

theorem coeffOf_nil (m : Mono) : coeffOf [] m = 0 := rfl

theorem coeffOf_append (p q : Poly) (m : Mono) :
    coeffOf (p ++ q) m = coeffOf p m + coeffOf q m := by
  induction p with
  | nil => simp [coeffOf, Gauss.zero_add]
  | cons t rest ih =>
    cases t with
    | mk a e =>
      simp only [List.cons_append, coeffOf, ih]
      rw [← Gauss.add_assoc]

def mulMono (a : Gauss) (m : Mono) : Poly → Poly
  | [] => []
  | (b, n) :: q => (a * b, m.mul n) :: mulMono a m q

def mul : Poly → Poly → Poly
  | [], _ => []
  | (a, m) :: p, q => mulMono a m q ++ mul p q

def factor (a : Gauss) (m : Mono) (q : Poly) (t : Mono) : Gauss :=
  match subExp t m with
  | none => 0
  | some n => a * coeffOf q n

theorem coeffOf_mulMono (a : Gauss) (m : Mono) (q : Poly) (t : Mono) :
    coeffOf (mulMono a m q) t = factor a m q t := by
  induction q with
  | nil =>
    cases hsub : subExp t m with
    | none => simp [mulMono, coeffOf, factor, hsub]
    | some _ => simp [mulMono, coeffOf, factor, hsub, Gauss.mul_zero]
  | cons head tail ih =>
    cases head with
    | mk b n =>
      simp only [mulMono, coeffOf, ih, factor]
      cases hsub : subExp t m with
      | none =>
        have hne : m.mul n ≠ t := by
          intro heq
          have hsome := subExp_mul m n
          rw [heq] at hsome
          simp [hsub] at hsome
        simp [hne, Gauss.zero_add]
      | some k =>
        have hmk : m.mul k = t := mul_subExp hsub
        by_cases hhead : m.mul n = t
        · have hn : n = k := by
            have hmul := congrArg (fun x => subExp x m) hhead
            rw [subExp_mul, hsub] at hmul
            exact Option.some.inj hmul
          subst hn
          simp [hhead, Gauss.mul_add]
        · have hnk : n ≠ k := by
            intro hn
            apply hhead
            rw [hn, hmk]
          simp [hhead, hnk, Gauss.zero_add]

def coeffSum : Poly → Poly → Mono → Gauss
  | [], _, _ => 0
  | (a, m) :: p, q, t => factor a m q t + coeffSum p q t

theorem coeffOf_mul (p q : Poly) (t : Mono) :
    coeffOf (mul p q) t = coeffSum p q t := by
  induction p with
  | nil => simp [mul, coeffOf, coeffSum]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [mul, coeffOf_append, coeffOf_mulMono, ih, coeffSum]

def single (a : Gauss) (m : Mono) : Poly := [(a, m)]

def cSq : Mono := ⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩
def sSq : Mono := ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩
def nxSq : Mono := ⟨0, 0, 2, 0, 0, 0, 0, 0, 0⟩
def nySq : Mono := ⟨0, 0, 0, 2, 0, 0, 0, 0, 0⟩
def nzSq : Mono := ⟨0, 0, 0, 0, 2, 0, 0, 0, 0⟩

/-- `c² + s² − 1`. -/
def gC : Poly := single 1 cSq ++ single 1 sSq ++ single (-1) Mono.one

/-- `nx² + ny² + nz² − 1`. -/
def gN : Poly := single 1 nxSq ++ single 1 nySq ++ single 1 nzSq ++ single (-1) Mono.one

def shiftC (m : Mono) : Mono := {m with c := m.c - 2}
def shiftS (m : Mono) : Mono := {m with s := m.s + 2}
def shiftNx (m : Mono) : Mono := {m with nx := m.nx - 2}
def shiftNy (m : Mono) : Mono := {m with ny := m.ny + 2}
def shiftNz (m : Mono) : Mono := {m with nz := m.nz + 2}

theorem shiftC_cSq (m : Mono) (h : 2 ≤ m.c) : (shiftC m).mul cSq = m := by
  ext
  · simp [shiftC, Mono.mul, cSq, Nat.sub_add_cancel h]
  · simp [shiftC, Mono.mul, cSq]
  · simp [shiftC, Mono.mul, cSq]
  · simp [shiftC, Mono.mul, cSq]
  · simp [shiftC, Mono.mul, cSq]
  · simp [shiftC, Mono.mul, cSq]
  · simp [shiftC, Mono.mul, cSq]
  · simp [shiftC, Mono.mul, cSq]
  · simp [shiftC, Mono.mul, cSq]

theorem shiftC_one (m : Mono) : (shiftC m).mul Mono.one = shiftC m := by
  ext <;> simp [shiftC, Mono.mul, Mono.one]

theorem shiftC_sSq (m : Mono) : (shiftC m).mul sSq = shiftS (shiftC m) := by
  ext <;> simp [shiftC, shiftS, Mono.mul, sSq]

def termWeight (m : Mono) : Nat := 3 ^ m.c * 2 ^ m.nx

def polyWeight : Poly → Nat
  | [] => 0
  | (a, m) :: rest => (if a = 0 then 0 else termWeight m) + polyWeight rest

/-- Un passo di peeling sul primo quadrato incontrato.

`some (resto, cofattore, true)` sbuccia `c`. `false` sbuccia `nx`.
-/
def peelFirst : Poly → Option (Poly × Poly × Bool)
  | [] => none
  | (a, m) :: rest =>
    if a = 0 then
      match peelFirst rest with
      | none => none
      | some (rest', cof, isC) => some ((a, m) :: rest', cof, isC)
    else if _h : 2 ≤ m.c then
      let m' := shiftC m
      some ([(a, m'), (-a, shiftS m')] ++ rest, single a m', true)
    else if _h : 2 ≤ m.nx then
      let m' := shiftNx m
      some (
        [(a, m'), (-a, shiftNy m'), (-a, shiftNz m')] ++ rest,
        single a m',
        false)
    else
      match peelFirst rest with
      | none => none
      | some (rest', cof, isC) => some ((a, m) :: rest', cof, isC)

def normal : Poly → Prop
  | [] => True
  | (a, m) :: rest => (a = 0 ∨ m.c < 2 ∧ m.nx < 2) ∧ normal rest

structure Split where
  rem : Poly
  fc : Poly
  fn : Poly

def assemble (s : Split) : Poly :=
  s.rem ++ mul s.fc gC ++ mul s.fn gN

def push (s : Split) (cof : Poly) (isC : Bool) : Split :=
  if isC then { s with fc := s.fc ++ cof } else { s with fn := s.fn ++ cof }

def reduceAux : Nat → Poly → Split
  | 0, p => ⟨p, [], []⟩
  | fuel + 1, p =>
    match peelFirst p with
    | none => ⟨p, [], []⟩
    | some (rest, cof, isC) => push (reduceAux fuel rest) cof isC

def reduce (p : Poly) : Split :=
  reduceAux (polyWeight p) p

theorem coeffSum_append (p q r : Poly) (t : Mono) :
    coeffSum (p ++ q) r t = coeffSum p r t + coeffSum q r t := by
  induction p with
  | nil => simp [coeffSum, Gauss.zero_add]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, coeffSum, ih]
      rw [← Gauss.add_assoc]

theorem polyWeight_append (p q : Poly) :
    polyWeight (p ++ q) = polyWeight p + polyWeight q := by
  induction p with
  | nil => simp [polyWeight]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, polyWeight, ih]
      rw [Nat.add_assoc]

theorem weight_zero_normal {p : Poly} (h : polyWeight p = 0) : normal p := by
  induction p with
  | nil => simp [normal]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      have hsum : (if a = 0 then 0 else termWeight m) + polyWeight rest = 0 := by
        simpa [polyWeight] using h
      have hrest : polyWeight rest = 0 := by omega
      have ha : a = 0 := by
        by_cases hz : a = 0
        · exact hz
        · have hpos : 0 < termWeight m := by
            simp only [termWeight]
            exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
          simp [hz] at hsum
          omega
      exact ⟨Or.inl ha, ih hrest⟩

theorem peel_none_normal {p : Poly} (h : peelFirst p = none) : normal p := by
  induction p with
  | nil => simp [normal]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      by_cases ha : a = 0
      · rw [peelFirst, ite_eq_left ha] at h
        cases hrest : peelFirst rest with
        | none =>
          exact ⟨Or.inl ha, ih hrest⟩
        | some val =>
          simp [hrest] at h
      · rw [peelFirst, ite_eq_right ha] at h
        by_cases hc : 2 ≤ m.c
        · rw [dite_eq_left hc] at h
          simp at h
        · rw [dite_eq_right hc] at h
          by_cases hnx : 2 ≤ m.nx
          · rw [dite_eq_left hnx] at h
            simp at h
          · rw [dite_eq_right hnx] at h
            cases hrest : peelFirst rest with
            | none =>
              exact ⟨Or.inr ⟨Nat.lt_of_not_ge hc, Nat.lt_of_not_ge hnx⟩, ih hrest⟩
            | some val =>
              simp [hrest] at h

theorem Gauss.one_ne_zero : (1 : Gauss) ≠ 0 := by
  intro h
  have hre : Gauss.re 1 = Gauss.re 0 := congrArg Gauss.re h
  simp at hre

theorem coeff_gC_cSq : coeffOf gC cSq = 1 := by
  have hs : sSq ≠ cSq := by decide
  have ho : Mono.one ≠ cSq := by decide
  simp [gC, single, coeffOf, hs, ho, Gauss.add_zero]

theorem coeff_gC_sSq : coeffOf gC sSq = 1 := by
  have hc : cSq ≠ sSq := by decide
  have ho : Mono.one ≠ sSq := by decide
  simp [gC, single, coeffOf, hc, ho, Gauss.add_zero, Gauss.zero_add]

theorem coeff_gC_one : coeffOf gC Mono.one = -1 := by
  have hc : cSq ≠ Mono.one := by decide
  have hs : sSq ≠ Mono.one := by decide
  simp [gC, single, coeffOf, hc, hs, Gauss.zero_add, Gauss.add_zero]

theorem coeff_gC_other (k : Mono) (hc : k ≠ cSq) (hs : k ≠ sSq) (ho : k ≠ Mono.one) :
    coeffOf gC k = 0 := by
  have hc' : cSq ≠ k := Ne.symm hc
  have hs' : sSq ≠ k := Ne.symm hs
  have ho' : Mono.one ≠ k := Ne.symm ho
  simp [gC, single, coeffOf, hc', hs', ho', Gauss.add_zero]

theorem m_ne_shiftC (m : Mono) (h : 2 ≤ m.c) : m ≠ shiftC m := by
  intro eq
  have := congrArg Mono.c eq
  simp [shiftC] at this
  omega

theorem m_ne_shiftS (m : Mono) (_h : 2 ≤ m.c) : m ≠ shiftS (shiftC m) := by
  intro eq
  have := congrArg Mono.s eq
  simp [shiftC, shiftS] at this

theorem shiftC_ne_shiftS (m : Mono) : shiftC m ≠ shiftS (shiftC m) := by
  intro eq
  have := congrArg Mono.s eq
  simp [shiftS] at this

theorem coeff_single_mul (a : Gauss) (m : Mono) (q : Poly) (t : Mono) :
    coeffOf (mul (single a m) q) t = factor a m q t := by
  rw [coeffOf_mul]
  simp [single, coeffSum, Gauss.add_zero]

theorem coeff_head_c (a : Gauss) (m : Mono) (h : 2 ≤ m.c) (t : Mono) :
    (if m = t then a else 0) =
      coeffOf
        ([(a, shiftC m), (-a, shiftS (shiftC m))] ++ mul (single a (shiftC m)) gC) t := by
  rw [coeffOf_append, coeff_single_mul]
  simp only [coeffOf, Gauss.add_zero]
  have hm : (shiftC m).mul cSq = m := shiftC_cSq m h
  have hs : (shiftC m).mul sSq = shiftS (shiftC m) := shiftC_sSq m
  have ho : (shiftC m).mul Mono.one = shiftC m := shiftC_one m
  by_cases ht : m = t
  · have hsub : subExp t (shiftC m) = some cSq := by
      rw [← ht]
      have h0 := subExp_mul (shiftC m) cSq
      rwa [hm] at h0
    have h1 : shiftC m ≠ t := by
      intro eq
      exact m_ne_shiftC m h (ht.trans eq.symm)
    have h2 : shiftS (shiftC m) ≠ t := by
      intro eq
      exact m_ne_shiftS m h (ht.trans eq.symm)
    rw [ite_eq_left ht, ite_eq_right h1, ite_eq_right h2]
    simp only [factor, hsub, coeff_gC_cSq, Gauss.mul_one, Gauss.zero_add]
  · by_cases hts : shiftS (shiftC m) = t
    · have hsub : subExp t (shiftC m) = some sSq := by
        rw [← hts]
        have h0 := subExp_mul (shiftC m) sSq
        rwa [hs] at h0
      have h1 : shiftC m ≠ t := by
        intro eq
        exact shiftC_ne_shiftS m (eq.trans hts.symm)
      rw [ite_eq_right ht, ite_eq_right h1, ite_eq_left hts]
      simp only [factor, hsub, coeff_gC_sSq, Gauss.mul_one, Gauss.zero_add, Gauss.neg_add_cancel]
    · by_cases hto : shiftC m = t
      · have hsub : subExp t (shiftC m) = some Mono.one := by
          rw [← hto]
          have h0 := subExp_mul (shiftC m) Mono.one
          rwa [ho] at h0
        rw [ite_eq_right ht, ite_eq_right hts, ite_eq_left hto]
        simp only [factor, hsub, coeff_gC_one, Gauss.mul_neg_one, Gauss.add_zero, Gauss.add_neg_cancel]
      · rw [ite_eq_right ht, ite_eq_right hts, ite_eq_right hto]
        cases hsub : subExp t (shiftC m) with
        | none =>
          simp only [factor, hsub, Gauss.zero_add]
        | some k =>
          have hmk : (shiftC m).mul k = t := mul_subExp hsub
          have hkc : k ≠ cSq := by
            intro hk
            exact ht (by rw [← hmk, hk, hm])
          have hks : k ≠ sSq := by
            intro hk
            exact hts (by rw [← hmk, hk, hs])
          have hko : k ≠ Mono.one := by
            intro hk
            exact hto (by rw [← hmk, hk, ho])
          simp only [factor, hsub, coeff_gC_other k hkc hks hko, Gauss.mul_zero, Gauss.zero_add]

theorem Gauss.neg_ne_zero {z : Gauss} (h : z ≠ 0) : -z ≠ 0 := by
  intro hz
  apply h
  have hz' := congrArg (fun w : Gauss => -w) hz
  rw [Gauss.neg_neg] at hz'
  have z0 : -(0 : Gauss) = 0 := by
    ext <;> simp <;> grind
  exact hz'.trans z0

theorem coeff_gN_nxSq : coeffOf gN nxSq = 1 := by
  have hy : nySq ≠ nxSq := by decide
  have hz : nzSq ≠ nxSq := by decide
  have ho : Mono.one ≠ nxSq := by decide
  simp [gN, single, coeffOf, hy, hz, ho, Gauss.add_zero]

theorem coeff_gN_nySq : coeffOf gN nySq = 1 := by
  have hx : nxSq ≠ nySq := by decide
  have hz : nzSq ≠ nySq := by decide
  have ho : Mono.one ≠ nySq := by decide
  simp [gN, single, coeffOf, hx, hz, ho, Gauss.add_zero, Gauss.zero_add]

theorem coeff_gN_nzSq : coeffOf gN nzSq = 1 := by
  have hx : nxSq ≠ nzSq := by decide
  have hy : nySq ≠ nzSq := by decide
  have ho : Mono.one ≠ nzSq := by decide
  simp [gN, single, coeffOf, hx, hy, ho, Gauss.add_zero, Gauss.zero_add]

theorem coeff_gN_one : coeffOf gN Mono.one = -1 := by
  have hx : nxSq ≠ Mono.one := by decide
  have hy : nySq ≠ Mono.one := by decide
  have hz : nzSq ≠ Mono.one := by decide
  simp [gN, single, coeffOf, hx, hy, hz, Gauss.zero_add, Gauss.add_zero]

theorem coeff_gN_other (k : Mono) (hx : k ≠ nxSq) (hy : k ≠ nySq) (hz : k ≠ nzSq)
    (ho : k ≠ Mono.one) : coeffOf gN k = 0 := by
  have hx' : nxSq ≠ k := Ne.symm hx
  have hy' : nySq ≠ k := Ne.symm hy
  have hz' : nzSq ≠ k := Ne.symm hz
  have ho' : Mono.one ≠ k := Ne.symm ho
  simp [gN, single, coeffOf, hx', hy', hz', ho', Gauss.add_zero]

theorem shiftNx_nxSq (m : Mono) (h : 2 ≤ m.nx) : (shiftNx m).mul nxSq = m := by
  ext
  · simp [shiftNx, Mono.mul, nxSq]
  · simp [shiftNx, Mono.mul, nxSq]
  · simp [shiftNx, Mono.mul, nxSq, Nat.sub_add_cancel h]
  · simp [shiftNx, Mono.mul, nxSq]
  · simp [shiftNx, Mono.mul, nxSq]
  · simp [shiftNx, Mono.mul, nxSq]
  · simp [shiftNx, Mono.mul, nxSq]
  · simp [shiftNx, Mono.mul, nxSq]
  · simp [shiftNx, Mono.mul, nxSq]

theorem shiftNx_one (m : Mono) : (shiftNx m).mul Mono.one = shiftNx m := by
  ext <;> simp [shiftNx, Mono.mul, Mono.one]

theorem shiftNx_nySq (m : Mono) : (shiftNx m).mul nySq = shiftNy (shiftNx m) := by
  ext <;> simp [shiftNx, shiftNy, Mono.mul, nySq]

theorem shiftNx_nzSq (m : Mono) : (shiftNx m).mul nzSq = shiftNz (shiftNx m) := by
  ext <;> simp [shiftNx, shiftNz, Mono.mul, nzSq]

theorem m_ne_shiftNx (m : Mono) (h : 2 ≤ m.nx) : m ≠ shiftNx m := by
  intro eq
  have := congrArg Mono.nx eq
  simp [shiftNx] at this
  omega

theorem m_ne_shiftNy (m : Mono) : m ≠ shiftNy (shiftNx m) := by
  intro eq
  have := congrArg Mono.ny eq
  simp [shiftNx, shiftNy] at this

theorem m_ne_shiftNz (m : Mono) : m ≠ shiftNz (shiftNx m) := by
  intro eq
  have := congrArg Mono.nz eq
  simp [shiftNx, shiftNz] at this

theorem shiftNx_ne_shiftNy (m : Mono) : shiftNx m ≠ shiftNy (shiftNx m) := by
  intro eq
  have := congrArg Mono.ny eq
  simp [shiftNy] at this

theorem shiftNx_ne_shiftNz (m : Mono) : shiftNx m ≠ shiftNz (shiftNx m) := by
  intro eq
  have := congrArg Mono.nz eq
  simp [shiftNz] at this

theorem shiftNy_ne_shiftNz (m : Mono) : shiftNy (shiftNx m) ≠ shiftNz (shiftNx m) := by
  intro eq
  have := congrArg Mono.ny eq
  simp [shiftNy, shiftNz] at this

theorem coeff_head_n (a : Gauss) (m : Mono) (h : 2 ≤ m.nx) (t : Mono) :
    (if m = t then a else 0) =
      coeffOf
        ([(a, shiftNx m), (-a, shiftNy (shiftNx m)), (-a, shiftNz (shiftNx m))] ++
          mul (single a (shiftNx m)) gN) t := by
  rw [coeffOf_append, coeff_single_mul]
  simp only [coeffOf, Gauss.add_zero]
  have hm : (shiftNx m).mul nxSq = m := shiftNx_nxSq m h
  have hy : (shiftNx m).mul nySq = shiftNy (shiftNx m) := shiftNx_nySq m
  have hz : (shiftNx m).mul nzSq = shiftNz (shiftNx m) := shiftNx_nzSq m
  have ho : (shiftNx m).mul Mono.one = shiftNx m := shiftNx_one m
  by_cases ht : m = t
  · have hsub : subExp t (shiftNx m) = some nxSq := by
      rw [← ht]
      have h0 := subExp_mul (shiftNx m) nxSq
      rwa [hm] at h0
    have h1 : shiftNx m ≠ t := fun eq => m_ne_shiftNx m h (ht.trans eq.symm)
    have h2 : shiftNy (shiftNx m) ≠ t := fun eq => m_ne_shiftNy m (ht.trans eq.symm)
    have h3 : shiftNz (shiftNx m) ≠ t := fun eq => m_ne_shiftNz m (ht.trans eq.symm)
    rw [ite_eq_left ht, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
    simp only [factor, hsub, coeff_gN_nxSq, Gauss.mul_one, Gauss.zero_add]
  · by_cases hny : shiftNy (shiftNx m) = t
    · have hsub : subExp t (shiftNx m) = some nySq := by
        rw [← hny]
        have h0 := subExp_mul (shiftNx m) nySq
        rwa [hy] at h0
      have h1 : shiftNx m ≠ t := fun eq => shiftNx_ne_shiftNy m (eq.trans hny.symm)
      have h3 : shiftNz (shiftNx m) ≠ t := fun eq => shiftNy_ne_shiftNz m (hny.trans eq.symm)
      rw [ite_eq_right ht, ite_eq_right h1, ite_eq_left hny, ite_eq_right h3]
      simp only [factor, hsub, coeff_gN_nySq, Gauss.mul_one, Gauss.zero_add, Gauss.add_zero,
        Gauss.neg_add_cancel]
    · by_cases hnz : shiftNz (shiftNx m) = t
      · have hsub : subExp t (shiftNx m) = some nzSq := by
          rw [← hnz]
          have h0 := subExp_mul (shiftNx m) nzSq
          rwa [hz] at h0
        have h1 : shiftNx m ≠ t := fun eq => shiftNx_ne_shiftNz m (eq.trans hnz.symm)
        rw [ite_eq_right ht, ite_eq_right h1, ite_eq_right hny, ite_eq_left hnz]
        simp only [factor, hsub, coeff_gN_nzSq, Gauss.mul_one, Gauss.zero_add, Gauss.neg_add_cancel]
      · by_cases hnx : shiftNx m = t
        · have hsub : subExp t (shiftNx m) = some Mono.one := by
            rw [← hnx]
            have h0 := subExp_mul (shiftNx m) Mono.one
            rwa [ho] at h0
          rw [ite_eq_right ht, ite_eq_right hny, ite_eq_right hnz, ite_eq_left hnx]
          simp only [factor, hsub, coeff_gN_one, Gauss.mul_neg_one, Gauss.add_zero, Gauss.add_neg_cancel]
        · rw [ite_eq_right ht, ite_eq_right hny, ite_eq_right hnz, ite_eq_right hnx]
          cases hsub : subExp t (shiftNx m) with
          | none =>
            simp only [factor, hsub, Gauss.zero_add]
          | some k =>
            have hmk : (shiftNx m).mul k = t := mul_subExp hsub
            have hkx : k ≠ nxSq := fun hk => ht (by rw [← hmk, hk, hm])
            have hky : k ≠ nySq := fun hk => hny (by rw [← hmk, hk, hy])
            have hkz : k ≠ nzSq := fun hk => hnz (by rw [← hmk, hk, hz])
            have hko : k ≠ Mono.one := fun hk => hnx (by rw [← hmk, hk, ho])
            simp only [factor, hsub, coeff_gN_other k hkx hky hkz hko, Gauss.mul_zero,
              Gauss.zero_add]

theorem coeffOf_rotate (kept tail extra : Poly) (t : Mono) :
    coeffOf (kept ++ extra) t + coeffOf tail t =
      coeffOf ((kept ++ tail) ++ extra) t := by
  simp only [coeffOf_append]
  have h1 := Gauss.add_assoc (coeffOf kept t) (coeffOf extra t) (coeffOf tail t)
  have h2 := Gauss.add_comm (coeffOf extra t) (coeffOf tail t)
  have h3 := Gauss.add_assoc (coeffOf kept t) (coeffOf tail t) (coeffOf extra t)
  exact h1.trans ((congrArg (fun z => coeffOf kept t + z) h2).trans h3.symm)

theorem peel_coeff (p : Poly) : ∀ rest cof isC,
    peelFirst p = some (rest, cof, isC) → ∀ t,
      coeffOf p t = coeffOf (rest ++ mul cof (if isC then gC else gN)) t := by
  induction p with
  | nil =>
    intro rest cof isC h t
    simp [peelFirst] at h
  | cons head tail ih =>
    intro rest cof isC h t
    cases head with
    | mk a m =>
      by_cases ha : a = 0
      · rw [peelFirst, ite_eq_left ha] at h
        cases htail : peelFirst tail with
        | none => simp [htail] at h
        | some val =>
          cases val with
          | mk rest' rest2 =>
            cases rest2 with
            | mk cof' isC' =>
              simp only [htail] at h
              injection h with h'
              injection h' with hr hpair
              injection hpair with hc hi
              subst hr hc hi
              simp only [coeffOf, List.cons_append, coeffOf_append, ih rest' cof' isC' htail t]
      · rw [peelFirst, ite_eq_right ha] at h
        by_cases hc : 2 ≤ m.c
        · rw [dite_eq_left hc] at h
          dsimp at h
          injection h with h'
          injection h' with hr hpair
          injection hpair with hcof hi
          subst hr hcof hi
          rw [coeffOf, coeff_head_c a m hc t]
          exact coeffOf_rotate [(a, shiftC m), (-a, shiftS (shiftC m))] tail
            (mul (single a (shiftC m)) gC) t
        · rw [dite_eq_right hc] at h
          by_cases hnx : 2 ≤ m.nx
          · rw [dite_eq_left hnx] at h
            dsimp at h
            injection h with h'
            injection h' with hr hpair
            injection hpair with hcof hi
            subst hr hcof hi
            rw [coeffOf, coeff_head_n a m hnx t]
            exact coeffOf_rotate
              [(a, shiftNx m), (-a, shiftNy (shiftNx m)), (-a, shiftNz (shiftNx m))] tail
              (mul (single a (shiftNx m)) gN) t
          · rw [dite_eq_right hnx] at h
            cases htail : peelFirst tail with
            | none => simp [htail] at h
            | some val =>
              cases val with
              | mk rest' rest2 =>
                cases rest2 with
                | mk cof' isC' =>
                  simp only [htail] at h
                  injection h with h'
                  injection h' with hr hpair
                  injection hpair with hcof hi
                  subst hr hcof hi
                  simp only [coeffOf, List.cons_append, coeffOf_append, ih rest' cof' isC' htail t]

theorem weight_peel_c (c nx : Nat) (hc : 2 ≤ c) :
    2 * 3 ^ (c - 2) * 2 ^ nx < 3 ^ c * 2 ^ nx := by
  have wpos : 0 < 3 ^ (c - 2) * 2 ^ nx :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have h9 : (3 : Nat) ^ 2 = 9 := by decide
  calc
    2 * 3 ^ (c - 2) * 2 ^ nx
        = 2 * (3 ^ (c - 2) * 2 ^ nx) := by rw [Nat.mul_assoc]
    _ < 9 * (3 ^ (c - 2) * 2 ^ nx) :=
        Nat.mul_lt_mul_of_pos_right (by decide : (2 : Nat) < 9) wpos
    _ = 3 ^ c * 2 ^ nx := by
        rw [← Nat.mul_assoc, Nat.mul_comm 9 (3 ^ (c - 2)), ← h9, ← Nat.pow_add,
          Nat.sub_add_cancel hc]

theorem weight_peel_n (c nx : Nat) (hnx : 2 ≤ nx) :
    3 * 3 ^ c * 2 ^ (nx - 2) < 3 ^ c * 2 ^ nx := by
  have wpos : 0 < 3 ^ c * 2 ^ (nx - 2) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  calc
    3 * 3 ^ c * 2 ^ (nx - 2)
        = 3 * (3 ^ c * 2 ^ (nx - 2)) := by rw [Nat.mul_assoc]
    _ < 4 * (3 ^ c * 2 ^ (nx - 2)) :=
        Nat.mul_lt_mul_of_pos_right (by decide : (3 : Nat) < 4) wpos
    _ = 3 ^ c * 2 ^ nx := by
        rw [← Nat.mul_assoc, Nat.mul_comm 4 (3 ^ c), Nat.mul_assoc, ← h4,
          Nat.mul_comm (2 ^ 2) (2 ^ (nx - 2)), ← Nat.pow_add, Nat.sub_add_cancel hnx]

theorem peel_weight (p : Poly) : ∀ rest cof isC,
    peelFirst p = some (rest, cof, isC) → polyWeight rest < polyWeight p := by
  induction p with
  | nil =>
    intro rest cof isC h
    simp [peelFirst] at h
  | cons head tail ih =>
    intro rest cof isC h
    cases head with
    | mk a m =>
      by_cases ha : a = 0
      · rw [peelFirst, ite_eq_left ha] at h
        cases htail : peelFirst tail with
        | none => simp [htail] at h
        | some val =>
          cases val with
          | mk rest' rest2 =>
            cases rest2 with
            | mk cof' isC' =>
              simp only [htail] at h
              injection h with h'
              injection h' with hr hpair
              injection hpair with hc hi
              subst hr hc hi
              simpa [polyWeight, ite_eq_left ha, Nat.zero_add] using ih rest' cof' isC' htail
      · rw [peelFirst, ite_eq_right ha] at h
        by_cases hc : 2 ≤ m.c
        · rw [dite_eq_left hc] at h
          dsimp at h
          injection h with h'
          injection h' with hr _hpair
          subst hr
          simp only [polyWeight, ite_eq_right ha, ite_eq_right (Gauss.neg_ne_zero ha), termWeight,
            shiftC, shiftS]
          rw [← Nat.add_assoc, ← Nat.two_mul, ← Nat.mul_assoc]
          exact Nat.add_lt_add_right (weight_peel_c m.c m.nx hc) (polyWeight tail)
        · rw [dite_eq_right hc] at h
          by_cases hnx : 2 ≤ m.nx
          · rw [dite_eq_left hnx] at h
            dsimp at h
            injection h with h'
            injection h' with hr _hpair
            subst hr
            simp only [polyWeight, ite_eq_right ha, ite_eq_right (Gauss.neg_ne_zero ha), termWeight,
              shiftNx, shiftNy, shiftNz]
            rw [← Nat.add_assoc, ← Nat.add_assoc, ← Nat.two_mul, ← Nat.succ_mul, ← Nat.mul_assoc]
            exact Nat.add_lt_add_right (weight_peel_n m.c m.nx hnx) (polyWeight tail)
          · rw [dite_eq_right hnx] at h
            cases htail : peelFirst tail with
            | none => simp [htail] at h
            | some val =>
              cases val with
              | mk rest' rest2 =>
                cases rest2 with
                | mk cof' isC' =>
                  simp only [htail] at h
                  injection h with h'
                  injection h' with hr hpair
                  injection hpair with hcof hi
                  subst hr hcof hi
                  simp only [polyWeight, ite_eq_right ha]
                  exact Nat.add_lt_add_left (ih rest' cof' isC' htail) (termWeight m)

theorem push_coeff (s : Split) (cof : Poly) (isC : Bool) (t : Mono) :
    coeffOf (assemble (push s cof isC)) t =
      coeffOf (assemble s) t + coeffOf (mul cof (if isC then gC else gN)) t := by
  cases isC with
  | true =>
    simp only [push]
    dsimp
    simp only [assemble, coeffOf_append, coeffOf_mul]
    rw [coeffSum_append]
    ext <;> simp <;> grind
  | false =>
    simp only [push]
    dsimp
    simp only [assemble, coeffOf_append, coeffOf_mul]
    rw [coeffSum_append]
    ext <;> simp <;> grind

theorem reduceAux_spec (fuel : Nat) (p : Poly) (h : polyWeight p ≤ fuel) :
    normal (reduceAux fuel p).rem ∧
      ∀ t, coeffOf p t = coeffOf (assemble (reduceAux fuel p)) t := by
  induction fuel generalizing p with
  | zero =>
    have hz : polyWeight p = 0 := by omega
    refine ⟨weight_zero_normal hz, ?_⟩
    intro t
    simp only [reduceAux, assemble, mul, List.append_nil]
  | succ fuel ih =>
    cases hpeel : peelFirst p with
    | none =>
      have hred : reduceAux (fuel + 1) p = ⟨p, [], []⟩ := by
        simp [reduceAux, hpeel]
      rw [hred]
      refine ⟨peel_none_normal hpeel, ?_⟩
      intro t
      simp only [assemble, mul, List.append_nil]
    | some val =>
      cases val with
      | mk rest rest2 =>
        cases rest2 with
        | mk cof isC =>
          have hlt : polyWeight rest < polyWeight p := peel_weight p rest cof isC hpeel
          have hle : polyWeight rest ≤ fuel := by omega
          have ih' := ih rest hle
          refine ⟨?_, ?_⟩
          · cases isC <;> simpa [reduceAux, hpeel, push] using ih'.1
          · intro t
            simp only [reduceAux, hpeel]
            rw [peel_coeff p rest cof isC hpeel t, coeffOf_append, ih'.2 t]
            exact (push_coeff (reduceAux fuel rest) cof isC t).symm

theorem reduce_normal (p : Poly) : normal (reduce p).rem :=
  (reduceAux_spec (polyWeight p) p (Nat.le_refl _)).1

theorem reduce_sound (p : Poly) (t : Mono) :
    coeffOf p t = coeffOf (assemble (reduce p)) t :=
  (reduceAux_spec (polyWeight p) p (Nat.le_refl _)).2 t

theorem peel_cons_none {a : Gauss} {m : Mono} {rest : Poly}
    (ha : a ≠ 0) (hc : ¬2 ≤ m.c) (hnx : ¬2 ≤ m.nx) (ht : peelFirst rest = none) :
    peelFirst ((a, m) :: rest) = none := by
  rw [peelFirst, ite_eq_right ha, dite_eq_right hc, dite_eq_right hnx, ht]

def gCRest : Poly :=
  [(1, Mono.one), (-1, sSq), (1, sSq), (-1, Mono.one)]

theorem peel_gC : peelFirst gC = some (gCRest, single 1 Mono.one, true) := by
  have hc : (2 : Nat) ≤ cSq.c := by decide
  unfold gC gCRest single
  simp only [List.cons_append, List.nil_append]
  rw [peelFirst, ite_eq_right Gauss.one_ne_zero, dite_eq_left hc]
  dsimp [shiftC, shiftS, cSq, sSq, Mono.one]
  rfl

theorem peel_gCRest : peelFirst gCRest = none := by
  unfold gCRest
  exact peel_cons_none Gauss.one_ne_zero (by decide) (by decide)
    (peel_cons_none (Gauss.neg_ne_zero Gauss.one_ne_zero) (by decide) (by decide)
      (peel_cons_none Gauss.one_ne_zero (by decide) (by decide)
        (peel_cons_none (Gauss.neg_ne_zero Gauss.one_ne_zero) (by decide) (by decide) rfl)))

theorem coeff_gCRest (t : Mono) : coeffOf gCRest t = 0 := by
  unfold gCRest
  simp only [coeffOf, Gauss.add_zero]
  by_cases ho : Mono.one = t
  · have hs : sSq ≠ t := fun eq => (by decide : sSq ≠ Mono.one) (eq.trans ho.symm)
    rw [ite_eq_left ho, ite_eq_right hs, ite_eq_right hs, ite_eq_left ho]
    simp only [Gauss.zero_add, Gauss.add_neg_cancel]
  · by_cases hs : sSq = t
    · rw [ite_eq_right ho, ite_eq_left hs, ite_eq_left hs, ite_eq_right ho]
      simp only [Gauss.add_zero, Gauss.neg_add_cancel]
    · rw [ite_eq_right ho, ite_eq_right hs, ite_eq_right hs, ite_eq_right ho]
      simp only [Gauss.zero_add]

theorem weight_gC_pos : 1 ≤ polyWeight gC := by
  unfold gC single
  simp only [List.cons_append, List.nil_append, polyWeight, ite_eq_right Gauss.one_ne_zero,
    ite_eq_right (Gauss.neg_ne_zero Gauss.one_ne_zero), termWeight, cSq, sSq, Mono.one]
  decide

theorem reduceAux_done {p : Poly} (h : peelFirst p = none) (fuel : Nat) :
    reduceAux fuel p = ⟨p, [], []⟩ := by
  cases fuel with
  | zero => rfl
  | succ _ => simp [reduceAux, h]

theorem reduce_gC_eq : reduce gC = ⟨gCRest, single 1 Mono.one, []⟩ := by
  have hfuel : 1 ≤ polyWeight gC := weight_gC_pos
  unfold reduce
  cases hpw : polyWeight gC with
  | zero => omega
  | succ n =>
    simp only [reduceAux, peel_gC]
    rw [reduceAux_done peel_gCRest n]
    rfl

theorem reduce_gC_rem (t : Mono) : coeffOf (reduce gC).rem t = 0 := by
  rw [reduce_gC_eq]
  exact coeff_gCRest t

theorem reduce_gC_cofactors : (reduce gC).fc = single 1 Mono.one ∧ (reduce gC).fn = [] := by
  rw [reduce_gC_eq]
  exact ⟨rfl, rfl⟩

def gNRest : Poly :=
  [(1, Mono.one), (-1, nySq), (-1, nzSq), (1, nySq), (1, nzSq), (-1, Mono.one)]

theorem peel_gN : peelFirst gN = some (gNRest, single 1 Mono.one, false) := by
  have hc : ¬(2 : Nat) ≤ nxSq.c := by decide
  have hnx : (2 : Nat) ≤ nxSq.nx := by decide
  unfold gN gNRest single
  simp only [List.cons_append, List.nil_append]
  rw [peelFirst, ite_eq_right Gauss.one_ne_zero, dite_eq_right hc, dite_eq_left hnx]
  dsimp [shiftNx, shiftNy, shiftNz, nxSq, nySq, nzSq, Mono.one]
  rfl

theorem peel_gNRest : peelFirst gNRest = none := by
  unfold gNRest
  exact peel_cons_none Gauss.one_ne_zero (by decide) (by decide)
    (peel_cons_none (Gauss.neg_ne_zero Gauss.one_ne_zero) (by decide) (by decide)
      (peel_cons_none (Gauss.neg_ne_zero Gauss.one_ne_zero) (by decide) (by decide)
        (peel_cons_none Gauss.one_ne_zero (by decide) (by decide)
          (peel_cons_none Gauss.one_ne_zero (by decide) (by decide)
            (peel_cons_none (Gauss.neg_ne_zero Gauss.one_ne_zero) (by decide) (by decide) rfl)))))

theorem coeff_gNRest (t : Mono) : coeffOf gNRest t = 0 := by
  unfold gNRest
  simp only [coeffOf, Gauss.add_zero]
  by_cases ho : Mono.one = t
  · have hy : nySq ≠ t := fun eq => (by decide : nySq ≠ Mono.one) (eq.trans ho.symm)
    have hz : nzSq ≠ t := fun eq => (by decide : nzSq ≠ Mono.one) (eq.trans ho.symm)
    rw [ite_eq_left ho, ite_eq_right hy, ite_eq_right hz, ite_eq_right hy, ite_eq_right hz,
      ite_eq_left ho]
    simp only [Gauss.zero_add, Gauss.add_neg_cancel]
  · by_cases hy : nySq = t
    · have h1 : Mono.one ≠ t := fun eq => (by decide : Mono.one ≠ nySq) (eq.trans hy.symm)
      have hz : nzSq ≠ t := fun eq => (by decide : nzSq ≠ nySq) (eq.trans hy.symm)
      rw [ite_eq_right h1, ite_eq_left hy, ite_eq_right hz, ite_eq_left hy, ite_eq_right hz,
        ite_eq_right h1]
      simp only [Gauss.zero_add, Gauss.add_zero, Gauss.neg_add_cancel]
    · by_cases hz : nzSq = t
      · have h1 : Mono.one ≠ t := fun eq => (by decide : Mono.one ≠ nzSq) (eq.trans hz.symm)
        rw [ite_eq_right h1, ite_eq_right hy, ite_eq_left hz, ite_eq_right hy, ite_eq_left hz,
          ite_eq_right h1]
        simp only [Gauss.zero_add, Gauss.add_zero, Gauss.neg_add_cancel]
      · rw [ite_eq_right ho, ite_eq_right hy, ite_eq_right hz, ite_eq_right hy, ite_eq_right hz,
          ite_eq_right ho]
        simp only [Gauss.zero_add]

theorem weight_gN_pos : 1 ≤ polyWeight gN := by
  unfold gN single
  simp only [List.cons_append, List.nil_append, polyWeight, ite_eq_right Gauss.one_ne_zero,
    ite_eq_right (Gauss.neg_ne_zero Gauss.one_ne_zero), termWeight, nxSq, nySq, nzSq, Mono.one]
  decide

theorem reduce_gN_eq : reduce gN = ⟨gNRest, [], single 1 Mono.one⟩ := by
  have hfuel : 1 ≤ polyWeight gN := weight_gN_pos
  unfold reduce
  cases hpw : polyWeight gN with
  | zero => omega
  | succ n =>
    simp only [reduceAux, peel_gN]
    rw [reduceAux_done peel_gNRest n]
    rfl

theorem reduce_gN_rem (t : Mono) : coeffOf (reduce gN).rem t = 0 := by
  rw [reduce_gN_eq]
  exact coeff_gNRest t

theorem reduce_gN_cofactors : (reduce gN).fc = [] ∧ (reduce gN).fn = single 1 Mono.one := by
  rw [reduce_gN_eq]
  exact ⟨rfl, rfl⟩

def arSq : Mono := ⟨0, 0, 0, 0, 0, 2, 0, 0, 0⟩
def aiSq : Mono := ⟨0, 0, 0, 0, 0, 0, 2, 0, 0⟩
def brSq : Mono := ⟨0, 0, 0, 0, 0, 0, 0, 2, 0⟩
def biSq : Mono := ⟨0, 0, 0, 0, 0, 0, 0, 0, 2⟩

/-- `ar² + ai² + br² + bi²`. -/
def amp : Poly := single 1 arSq ++ single 1 aiSq ++ single 1 brSq ++ single 1 biSq

/-- `ar² + ai² + br² + bi² − 1`. Non è un generatore di `reduce`. -/
def gA : Poly := amp ++ single (-1) Mono.one

end Universe.Quotient
