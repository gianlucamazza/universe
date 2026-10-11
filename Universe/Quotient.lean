/-
Quoziente a due quadrati, con cofattori.

Un polinomio è una lista di termini
`coefficiente · c^c s^s nx^nx ny^ny nz^nz ar^ar ai^ai br^br bi^bi a2r^a2r a2i^a2i a3r^a3r a3i^a3i c2^c2 s2^s2 mx^mx my^my mz^mz`.
`ar ai br bi a2r a2i a3r a3i c2 s2 mx my mz` non entrano in `reduce` né in `monoVal`;
`monoVal2` legge anche `c2 s2`, `monoVal3` anche `mx my mz`.
`reduce` sbuccia solo `c²` e `nx²`. `gA` è il terzo generatore, la sfera delle
ampiezze, e non entra in `reduce`.
- `c² = (1 − s²) + (c² + s² − 1)`
- `nx² = (1 − ny² − nz²) + (nx² + ny² + nz² − 1)`

`reduce` restituisce `resto`, `f`, `g`. Il teorema `reduce_sound` dice che, per ogni
polinomio e ogni monomio, i coefficienti coincidono:

`p = resto + f · (c² + s² − 1) + g · (nx² + ny² + nz² − 1)`.

Se il resto ha tutti i coefficienti zero, `p` sta nell'ideale. Il converso,
per questo `reduce`, è `Universe.Dynamics.reduce_complete`.
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
  a2r : Nat
  a2i : Nat
  a3r : Nat
  a3i : Nat
  c2 : Nat
  s2 : Nat
  mx : Nat
  my : Nat
  mz : Nat
  deriving DecidableEq, Repr

namespace Mono

abbrev one : Mono where
  c := 0
  s := 0
  nx := 0
  ny := 0
  nz := 0
  ar := 0
  ai := 0
  br := 0
  bi := 0
  a2r := 0
  a2i := 0
  a3r := 0
  a3i := 0
  c2 := 0
  s2 := 0
  mx := 0
  my := 0
  mz := 0

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
  a2r := m.a2r + n.a2r
  a2i := m.a2i + n.a2i
  a3r := m.a3r + n.a3r
  a3i := m.a3i + n.a3i
  c2 := m.c2 + n.c2
  s2 := m.s2 + n.s2
  mx := m.mx + n.mx
  my := m.my + n.my
  mz := m.mz + n.mz

end Mono

def subExp (t m : Mono) : Option Mono :=
  if _h : m.c ≤ t.c ∧ m.s ≤ t.s ∧ m.nx ≤ t.nx ∧ m.ny ≤ t.ny ∧ m.nz ≤ t.nz ∧
      m.ar ≤ t.ar ∧ m.ai ≤ t.ai ∧ m.br ≤ t.br ∧ m.bi ≤ t.bi ∧
      m.a2r ≤ t.a2r ∧ m.a2i ≤ t.a2i ∧ m.a3r ≤ t.a3r ∧ m.a3i ≤ t.a3i ∧
      m.c2 ≤ t.c2 ∧ m.s2 ≤ t.s2 ∧ m.mx ≤ t.mx ∧ m.my ≤ t.my ∧ m.mz ≤ t.mz then
    some ⟨t.c - m.c, t.s - m.s, t.nx - m.nx, t.ny - m.ny, t.nz - m.nz,
      t.ar - m.ar, t.ai - m.ai, t.br - m.br, t.bi - m.bi,
      t.a2r - m.a2r, t.a2i - m.a2i, t.a3r - m.a3r, t.a3i - m.a3i,
      t.c2 - m.c2, t.s2 - m.s2, t.mx - m.mx, t.my - m.my, t.mz - m.mz⟩
  else
    none

theorem subExp_mul (m n : Mono) : subExp (m.mul n) m = some n := by
  unfold subExp
  split
  · apply congrArg some
    ext <;> simp [Mono.mul, Nat.add_sub_cancel_left]
  · rename_i hle
    simp only [Mono.mul] at hle
    omega

theorem mul_subExp {t m k : Mono} (h : subExp t m = some k) : m.mul k = t := by
  unfold subExp at h
  split at h
  · rename_i hle
    cases h
    ext <;> simp only [Mono.mul] <;> omega
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

def cSq : Mono := {Mono.one with c := 2}
def sSq : Mono := {Mono.one with s := 2}
def nxSq : Mono := {Mono.one with nx := 2}
def nySq : Mono := {Mono.one with ny := 2}
def nzSq : Mono := {Mono.one with nz := 2}

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
  ext <;> simp [shiftC, Mono.mul, cSq, Nat.sub_add_cancel h]

theorem shiftC_one (m : Mono) : (shiftC m).mul Mono.one = shiftC m := by
  ext <;> simp [shiftC, Mono.mul]

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
  ext <;> simp [shiftNx, Mono.mul, nxSq, Nat.sub_add_cancel h]

theorem shiftNx_one (m : Mono) : (shiftNx m).mul Mono.one = shiftNx m := by
  ext <;> simp [shiftNx, Mono.mul]

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

/-! ### Divisione monica per `gC` e per `gN`

`gC` è monico di grado 2 in `c`, `gN` in `nx`. Le due variabili sono disgiunte.
`reduceC` sbuccia solo `c²`. Le fette `sliceC` e `sliceNx` isolano un esponente.
Il resto normale di un elemento dell'ideale ha coefficienti zero: è
`Universe.Dynamics.reduce_complete`. -/

def gC0 : Poly := single 1 sSq ++ single (-1) Mono.one

def gN0 : Poly := single 1 nySq ++ single 1 nzSq ++ single (-1) Mono.one

theorem gC_eq_split : gC = single 1 cSq ++ gC0 := by
  simp [gC, gC0, single]

theorem gN_eq_split : gN = single 1 nxSq ++ gN0 := by
  simp [gN, gN0, single]

def cSmall (p : Poly) : Prop := ∀ t, 2 ≤ t.c → coeffOf p t = 0

def nxSmall (p : Poly) : Prop := ∀ t, 2 ≤ t.nx → coeffOf p t = 0

def cListSmall : Poly → Prop
  | [] => True
  | (a, m) :: rest => (a = 0 ∨ m.c < 2) ∧ cListSmall rest

def nxListSmall : Poly → Prop
  | [] => True
  | (a, m) :: rest => (a = 0 ∨ m.nx < 2) ∧ nxListSmall rest

def listCFree : Poly → Prop
  | [] => True
  | (_, m) :: rest => m.c = 0 ∧ listCFree rest

def listNxFree : Poly → Prop
  | [] => True
  | (_, m) :: rest => m.nx = 0 ∧ listNxFree rest

theorem listCFree_gC0 : listCFree gC0 := by
  simp [listCFree, gC0, single, sSq, Mono.one]

theorem listCFree_gN : listCFree gN := by
  simp [listCFree, gN, single, nxSq, nySq, nzSq, Mono.one]

theorem listNxFree_gN0 : listNxFree gN0 := by
  simp [listNxFree, gN0, single, nySq, nzSq, Mono.one]

theorem listNxFree_gC : listNxFree gC := by
  simp [listNxFree, gC, single, cSq, sSq, Mono.one]

theorem cListSmall_append {p q : Poly} (hp : cListSmall p) (hq : cListSmall q) :
    cListSmall (p ++ q) := by
  induction p with
  | nil => simpa using hq
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases hp with ⟨hm, hrest⟩
      exact ⟨hm, ih hrest⟩

theorem cListSmall_cSmall {p : Poly} (h : cListSmall p) : cSmall p := by
  intro t ht
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases h with ⟨hm, hrest⟩
      by_cases he : m = t
      · have ha : a = 0 := by
          cases hm with
          | inl ha => exact ha
          | inr hlt =>
            have hc : m.c = t.c := congrArg Mono.c he
            omega
        simp [coeffOf, he, ha, Gauss.zero_add, ih hrest]
      · simp [coeffOf, he, Gauss.zero_add, ih hrest]

theorem nxListSmall_nxSmall {p : Poly} (h : nxListSmall p) : nxSmall p := by
  intro t ht
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases h with ⟨hm, hrest⟩
      by_cases he : m = t
      · have ha : a = 0 := by
          cases hm with
          | inl ha => exact ha
          | inr hlt =>
            have hx : m.nx = t.nx := congrArg Mono.nx he
            omega
        simp [coeffOf, he, ha, Gauss.zero_add, ih hrest]
      · simp [coeffOf, he, Gauss.zero_add, ih hrest]

theorem normal_cListSmall {p : Poly} (h : normal p) : cListSmall p := by
  induction p with
  | nil => simp [cListSmall]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases h with ⟨hm, hrest⟩
      refine ⟨?_, ih hrest⟩
      cases hm with
      | inl ha => exact Or.inl ha
      | inr hlt => exact Or.inr hlt.1

theorem normal_nxListSmall {p : Poly} (h : normal p) : nxListSmall p := by
  induction p with
  | nil => simp [nxListSmall]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases h with ⟨hm, hrest⟩
      refine ⟨?_, ih hrest⟩
      cases hm with
      | inl ha => exact Or.inl ha
      | inr hlt => exact Or.inr hlt.2

theorem cListSmall_mulMono {a : Gauss} {m : Mono} {q : Poly}
    (ha : a = 0 ∨ m.c < 2) (hq : listCFree q) : cListSmall (mulMono a m q) := by
  induction q with
  | nil => simp [mulMono, cListSmall]
  | cons head rest ih =>
    cases head with
    | mk b n =>
      rcases hq with ⟨hn, hrest⟩
      refine ⟨?_, ih hrest⟩
      cases ha with
      | inl hz => exact Or.inl (by rw [hz, Gauss.zero_mul])
      | inr hc =>
        have hc' : (m.mul n).c = m.c := by simp [Mono.mul, hn]
        exact Or.inr (hc' ▸ hc)

theorem cListSmall_mul {p q : Poly} (hp : cListSmall p) (hq : listCFree q) :
    cListSmall (mul p q) := by
  induction p with
  | nil => simp [mul, cListSmall]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases hp with ⟨hm, hrest⟩
      simpa [mul] using cListSmall_append (cListSmall_mulMono hm hq) (ih hrest)

def setC (k : Nat) (m : Mono) : Mono := {m with c := k}

def setNx (k : Nat) (m : Mono) : Mono := {m with nx := k}

theorem Mono.mul_right_cancel {a b c : Mono} (h : b.mul a = c.mul a) : b = c := by
  rw [Mono.ext_iff]
  simp only [Mono.mul, Mono.mk.injEq, Nat.add_right_cancel_iff] at h
  exact h

def sliceC (k : Nat) : Poly → Poly
  | [] => []
  | (a, m) :: rest => if m.c = k then (a, setC 0 m) :: sliceC k rest else sliceC k rest

def sliceNx (k : Nat) : Poly → Poly
  | [] => []
  | (a, m) :: rest => if m.nx = k then (a, setNx 0 m) :: sliceNx k rest else sliceNx k rest

def cBound : Poly → Nat
  | [] => 0
  | (_, m) :: rest => max m.c (cBound rest)

def nxBound : Poly → Nat
  | [] => 0
  | (_, m) :: rest => max m.nx (nxBound rest)

theorem sliceC_above {p : Poly} {k : Nat} (hk : cBound p < k) : sliceC k p = [] := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk _a m =>
      have hmax : max m.c (cBound rest) < k := by simpa [cBound] using hk
      have hne : m.c ≠ k := Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax)
      simp [sliceC, hne, ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax)]

theorem sliceNx_above {p : Poly} {k : Nat} (hk : nxBound p < k) : sliceNx k p = [] := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk _a m =>
      have hmax : max m.nx (nxBound rest) < k := by simpa [nxBound] using hk
      have hne : m.nx ≠ k := Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax)
      simp [sliceNx, hne, ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax)]

theorem coeff_sliceC (k : Nat) (p : Poly) (t : Mono) :
    coeffOf (sliceC k p) t = if t.c = 0 then coeffOf p (setC k t) else 0 := by
  induction p with
  | nil => simp [sliceC, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [sliceC]
      by_cases hc : m.c = k
      · simp only [hc, ite_true, coeffOf, ih]
        by_cases ht : t.c = 0
        · simp only [ht, ite_true]
          by_cases he : setC 0 m = t
          · have hrestore : setC 0 (setC k t) = t := by
              ext <;> simp [setC, ht]
            have hm : m = setC k t := by
              rw [← he]
              ext <;> simp [setC, hc]
            simp [hm, hrestore]
          · have hm : m ≠ setC k t := by
              intro eq
              apply he
              have hrestore : setC 0 (setC k t) = t := by
                ext <;> simp [setC, ht]
              rw [eq]; exact hrestore
            simp [he, hm, Gauss.zero_add]
        · have hne : setC 0 m ≠ t := by
            intro eq
            exact ht (Eq.symm (by simpa [setC] using congrArg Mono.c eq))
          simp [ht, hne, Gauss.zero_add]
      · simp only [hc, ite_false, coeffOf, ih]
        by_cases ht : t.c = 0
        · have hm : m ≠ setC k t := by
            intro eq
            exact hc (by simpa [setC] using congrArg Mono.c eq)
          simp [ht, hm, Gauss.zero_add]
        · simp [ht]

theorem coeff_sliceNx (k : Nat) (p : Poly) (t : Mono) :
    coeffOf (sliceNx k p) t = if t.nx = 0 then coeffOf p (setNx k t) else 0 := by
  induction p with
  | nil => simp [sliceNx, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [sliceNx]
      by_cases hx : m.nx = k
      · simp only [hx, ite_true, coeffOf, ih]
        by_cases ht : t.nx = 0
        · simp only [ht, ite_true]
          by_cases he : setNx 0 m = t
          · have hrestore : setNx 0 (setNx k t) = t := by
              ext <;> simp [setNx, ht]
            have hm : m = setNx k t := by
              rw [← he]
              ext <;> simp [setNx, hx]
            simp [hm, hrestore]
          · have hm : m ≠ setNx k t := by
              intro eq
              apply he
              have hrestore : setNx 0 (setNx k t) = t := by
                ext <;> simp [setNx, ht]
              rw [eq]; exact hrestore
            simp [he, hm, Gauss.zero_add]
        · have hne : setNx 0 m ≠ t := by
            intro eq
            exact ht (Eq.symm (by simpa [setNx] using congrArg Mono.nx eq))
          simp [ht, hne, Gauss.zero_add]
      · simp only [hx, ite_false, coeffOf, ih]
        by_cases ht : t.nx = 0
        · have hm : m ≠ setNx k t := by
            intro eq
            exact hx (by simpa [setNx] using congrArg Mono.nx eq)
          simp [ht, hm, Gauss.zero_add]
        · simp [ht]

theorem coeff_via_sliceC (p : Poly) (t : Mono) :
    coeffOf p t = coeffOf (sliceC t.c p) (setC 0 t) := by
  rw [coeff_sliceC]
  have h0 : (setC 0 t).c = 0 := rfl
  simp only [h0, ite_true]
  congr 1

theorem coeff_via_sliceNx (p : Poly) (t : Mono) :
    coeffOf p t = coeffOf (sliceNx t.nx p) (setNx 0 t) := by
  rw [coeff_sliceNx]
  have h0 : (setNx 0 t).nx = 0 := rfl
  simp only [h0, ite_true]
  congr 1

theorem sliceC_append (k : Nat) (p q : Poly) :
    sliceC k (p ++ q) = sliceC k p ++ sliceC k q := by
  induction p with
  | nil => simp [sliceC]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, sliceC]
      by_cases hc : m.c = k <;> simp [hc, ih]

theorem sliceNx_append (k : Nat) (p q : Poly) :
    sliceNx k (p ++ q) = sliceNx k p ++ sliceNx k q := by
  induction p with
  | nil => simp [sliceNx]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, sliceNx]
      by_cases hx : m.nx = k <;> simp [hx, ih]

theorem mulMono_append_eq (a : Gauss) (m : Mono) (p q : Poly) :
    mulMono a m (p ++ q) = mulMono a m p ++ mulMono a m q := by
  induction p with
  | nil => simp [mulMono]
  | cons head rest ih =>
    cases head with
    | mk b n => simp [mulMono, ih]

theorem mul_append_right_coeff (p q r : Poly) (t : Mono) :
    coeffOf (mul p (q ++ r)) t = coeffOf (mul p q ++ mul p r) t := by
  induction p with
  | nil => simp [mul, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show mul ((a, m) :: rest) (q ++ r) =
        mulMono a m (q ++ r) ++ mul rest (q ++ r) from rfl]
      rw [mulMono_append_eq, coeffOf_append, ih]
      rw [show mul ((a, m) :: rest) q = mulMono a m q ++ mul rest q from rfl,
        show mul ((a, m) :: rest) r = mulMono a m r ++ mul rest r from rfl]
      rw [coeffOf_append (mulMono a m q) (mulMono a m r),
        coeffOf_append (mul rest q) (mul rest r),
        coeffOf_append (mulMono a m q ++ mul rest q) (mulMono a m r ++ mul rest r),
        coeffOf_append (mulMono a m q) (mul rest q),
        coeffOf_append (mulMono a m r) (mul rest r)]
      -- (A + B) + (C + D) = (A + C) + (B + D)
      have hswap : ∀ (w x y z : Gauss), w + x + (y + z) = w + y + (x + z) := by
        intro w x y z
        ext <;> simp <;> grind
      exact hswap _ _ _ _

theorem factor_cSq (a : Gauss) (n m : Mono) :
    factor a n (single (1 : Gauss) cSq) (m.mul cSq) = if n = m then a else 0 := by
  by_cases hn : n = m
  · rw [hn]
    have hsub : subExp (m.mul cSq) m = some cSq := subExp_mul m cSq
    simp [factor, hsub, single, coeffOf, Gauss.mul_one, Gauss.add_zero]
  · cases hsub : subExp (m.mul cSq) n with
    | none => simp [factor, hsub, hn]
    | some k =>
      have hmk : n.mul k = m.mul cSq := mul_subExp hsub
      by_cases hk : k = cSq
      · exact absurd (Mono.mul_right_cancel (by simpa [hk] using hmk)) hn
      · have hne : cSq ≠ k := fun eq => hk eq.symm
        simp [factor, hsub, single, coeffOf, hne, hn, Gauss.zero_add, Gauss.mul_zero]

theorem factor_nxSq (a : Gauss) (n m : Mono) :
    factor a n (single (1 : Gauss) nxSq) (m.mul nxSq) = if n = m then a else 0 := by
  by_cases hn : n = m
  · rw [hn]
    have hsub : subExp (m.mul nxSq) m = some nxSq := subExp_mul m nxSq
    simp [factor, hsub, single, coeffOf, Gauss.mul_one, Gauss.add_zero]
  · cases hsub : subExp (m.mul nxSq) n with
    | none => simp [factor, hsub, hn]
    | some k =>
      have hmk : n.mul k = m.mul nxSq := mul_subExp hsub
      by_cases hk : k = nxSq
      · exact absurd (Mono.mul_right_cancel (by simpa [hk] using hmk)) hn
      · have hne : nxSq ≠ k := fun eq => hk eq.symm
        simp [factor, hsub, single, coeffOf, hne, hn, Gauss.zero_add, Gauss.mul_zero]

theorem coeff_mul_cSq_shift (f : Poly) (m : Mono) :
    coeffOf (mul f (single (1 : Gauss) cSq)) (m.mul cSq) = coeffOf f m := by
  induction f with
  | nil => simp [mul, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a n =>
      rw [show mul ((a, n) :: rest) (single (1 : Gauss) cSq) =
        mulMono a n (single (1 : Gauss) cSq) ++ mul rest (single (1 : Gauss) cSq) from rfl]
      rw [coeffOf_append, coeffOf_mulMono, ih, coeffOf, factor_cSq]

theorem coeff_mul_nxSq_shift (f : Poly) (m : Mono) :
    coeffOf (mul f (single (1 : Gauss) nxSq)) (m.mul nxSq) = coeffOf f m := by
  induction f with
  | nil => simp [mul, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a n =>
      rw [show mul ((a, n) :: rest) (single (1 : Gauss) nxSq) =
        mulMono a n (single (1 : Gauss) nxSq) ++ mul rest (single (1 : Gauss) nxSq) from rfl]
      rw [coeffOf_append, coeffOf_mulMono, ih, coeffOf, factor_nxSq]

theorem setC_mul_cSq (k : Nat) (t : Mono) :
    setC (k + 2) t = (setC k t).mul cSq := by
  ext <;> simp [setC, Mono.mul, cSq]

theorem setNx_mul_nxSq (k : Nat) (t : Mono) :
    setNx (k + 2) t = (setNx k t).mul nxSq := by
  ext <;> simp [setNx, Mono.mul, nxSq]

theorem coeff_slice_mul_cSq (k : Nat) (f : Poly) (t : Mono) :
    coeffOf (sliceC (k + 2) (mul f (single (1 : Gauss) cSq))) t = coeffOf (sliceC k f) t := by
  rw [coeff_sliceC, coeff_sliceC]
  by_cases ht : t.c = 0
  · simp only [ht, ite_true]
    rw [setC_mul_cSq k t, coeff_mul_cSq_shift]
  · simp [ht]

theorem coeff_slice_mul_nxSq (k : Nat) (f : Poly) (t : Mono) :
    coeffOf (sliceNx (k + 2) (mul f (single (1 : Gauss) nxSq))) t =
      coeffOf (sliceNx k f) t := by
  rw [coeff_sliceNx, coeff_sliceNx]
  by_cases ht : t.nx = 0
  · simp only [ht, ite_true]
    rw [setNx_mul_nxSq k t, coeff_mul_nxSq_shift]
  · simp [ht]

theorem setC_mul_free {m n : Mono} (hn : n.c = 0) : setC 0 (m.mul n) = (setC 0 m).mul n := by
  ext <;> simp [setC, Mono.mul, hn]

theorem setNx_mul_free {m n : Mono} (hn : n.nx = 0) :
    setNx 0 (m.mul n) = (setNx 0 m).mul n := by
  ext <;> simp [setNx, Mono.mul, hn]

theorem coeff_slice_mulMono_cFree (a : Gauss) (m : Mono) (q : Poly) (hq : listCFree q)
    (k : Nat) (t : Mono) :
    coeffOf (sliceC k (mulMono a m q)) t =
      if m.c = k then coeffOf (mulMono a (setC 0 m) q) t else 0 := by
  induction q with
  | nil => simp [mulMono, sliceC, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk b n =>
      rcases hq with ⟨hn, hrest⟩
      have hc : (m.mul n).c = m.c := by simp [Mono.mul, hn]
      simp only [mulMono]
      by_cases hk : m.c = k
      · have hc' : (m.mul n).c = k := hc.trans hk
        simp only [sliceC, hc', ite_true, coeffOf, ih hrest, hk, ite_true]
        have hhead : setC 0 (m.mul n) = (setC 0 m).mul n := setC_mul_free hn
        by_cases he : setC 0 (m.mul n) = t
        · rw [← hhead, he]
        · have he' : (setC 0 m).mul n ≠ t := by rw [← hhead]; exact he
          simp [he, he', Gauss.zero_add]
      · have hc' : (m.mul n).c ≠ k := by
          intro eq
          exact hk (hc.symm.trans eq)
        simp only [sliceC, hc', ite_false, ih hrest, hk, ite_false]

theorem coeff_slice_mulMono_nxFree (a : Gauss) (m : Mono) (q : Poly) (hq : listNxFree q)
    (k : Nat) (t : Mono) :
    coeffOf (sliceNx k (mulMono a m q)) t =
      if m.nx = k then coeffOf (mulMono a (setNx 0 m) q) t else 0 := by
  induction q with
  | nil => simp [mulMono, sliceNx, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk b n =>
      rcases hq with ⟨hn, hrest⟩
      have hx : (m.mul n).nx = m.nx := by simp [Mono.mul, hn]
      simp only [mulMono]
      by_cases hk : m.nx = k
      · have hx' : (m.mul n).nx = k := hx.trans hk
        simp only [sliceNx, hx', ite_true, coeffOf, ih hrest, hk, ite_true]
        have hhead : setNx 0 (m.mul n) = (setNx 0 m).mul n := setNx_mul_free hn
        by_cases he : setNx 0 (m.mul n) = t
        · rw [← hhead, he]
        · have he' : (setNx 0 m).mul n ≠ t := by rw [← hhead]; exact he
          simp [he, he', Gauss.zero_add]
      · have hx' : (m.mul n).nx ≠ k := by
          intro eq
          exact hk (hx.symm.trans eq)
        simp only [sliceNx, hx', ite_false, ih hrest, hk, ite_false]

theorem coeff_slice_mul_cFree (k : Nat) (p q : Poly) (hq : listCFree q) (t : Mono) :
    coeffOf (sliceC k (mul p q)) t = coeffOf (mul (sliceC k p) q) t := by
  induction p with
  | nil => simp [mul, sliceC, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      have hmul : mul ((a, m) :: rest) q = mulMono a m q ++ mul rest q := rfl
      rw [hmul, sliceC_append, coeffOf_append, coeff_slice_mulMono_cFree a m q hq k t, ih]
      simp only [sliceC]
      by_cases hk : m.c = k
      · simp only [hk, ite_true]
        rw [show mul ((a, setC 0 m) :: sliceC k rest) q =
          mulMono a (setC 0 m) q ++ mul (sliceC k rest) q from rfl]
        rw [coeffOf_append]
      · simp only [hk, ite_false, Gauss.zero_add]

theorem coeff_slice_mul_nxFree (k : Nat) (p q : Poly) (hq : listNxFree q) (t : Mono) :
    coeffOf (sliceNx k (mul p q)) t = coeffOf (mul (sliceNx k p) q) t := by
  induction p with
  | nil => simp [mul, sliceNx, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      have hmul : mul ((a, m) :: rest) q = mulMono a m q ++ mul rest q := rfl
      rw [hmul, sliceNx_append, coeffOf_append, coeff_slice_mulMono_nxFree a m q hq k t, ih]
      simp only [sliceNx]
      by_cases hx : m.nx = k
      · simp only [hx, ite_true]
        rw [show mul ((a, setNx 0 m) :: sliceNx k rest) q =
          mulMono a (setNx 0 m) q ++ mul (sliceNx k rest) q from rfl]
        rw [coeffOf_append]
      · simp only [hx, ite_false, Gauss.zero_add]

theorem sliceC_list_cFree (k : Nat) (p : Poly) : listCFree (sliceC k p) := by
  induction p with
  | nil => simp [sliceC, listCFree]
  | cons head rest ih =>
    cases head with
    | mk _a m =>
      simp only [sliceC]
      by_cases hc : m.c = k
      · simp only [hc, ite_true, listCFree]
        exact ⟨rfl, ih⟩
      · simp [hc, ih]

theorem sliceNx_list_nxFree (k : Nat) (p : Poly) : listNxFree (sliceNx k p) := by
  induction p with
  | nil => simp [sliceNx, listNxFree]
  | cons head rest ih =>
    cases head with
    | mk _a m =>
      simp only [sliceNx]
      by_cases hx : m.nx = k
      · simp only [hx, ite_true, listNxFree]
        exact ⟨rfl, ih⟩
      · simp [hx, ih]

theorem coeff_listCFree_zero {q : Poly} (hq : listCFree q) {k : Mono} (hk : k.c ≠ 0) :
    coeffOf q k = 0 := by
  induction q with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases hq with ⟨hm, hrest⟩
      have hne : m ≠ k := fun eq => hk (eq ▸ hm)
      simp [coeffOf, hne, Gauss.zero_add, ih hrest]

theorem coeff_listNxFree_zero {q : Poly} (hq : listNxFree q) {k : Mono} (hk : k.nx ≠ 0) :
    coeffOf q k = 0 := by
  induction q with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases hq with ⟨hm, hrest⟩
      have hne : m ≠ k := fun eq => hk (eq ▸ hm)
      simp [coeffOf, hne, Gauss.zero_add, ih hrest]

theorem listCFree_mul {p q : Poly} (hp : listCFree p) (hq : listCFree q) (t : Mono)
    (ht : t.c ≠ 0) : coeffOf (mul p q) t = 0 := by
  induction p with
  | nil => simp [mul, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases hp with ⟨hm, hrest⟩
      rw [show mul ((a, m) :: rest) q = mulMono a m q ++ mul rest q from rfl]
      rw [coeffOf_append, coeffOf_mulMono, ih hrest, Gauss.add_zero]
      cases hsub : subExp t m with
      | none => simp [factor, hsub]
      | some k =>
        have hk : k.c ≠ 0 := by
          intro hk0
          have hc : t.c = 0 := by
            have h := congrArg Mono.c (mul_subExp hsub)
            simp only [Mono.mul, hm, hk0] at h
            simpa [Nat.zero_add] using h.symm
          exact ht hc
        simp [factor, hsub, coeff_listCFree_zero hq hk, Gauss.mul_zero]

theorem listNxFree_mul {p q : Poly} (hp : listNxFree p) (hq : listNxFree q) (t : Mono)
    (ht : t.nx ≠ 0) : coeffOf (mul p q) t = 0 := by
  induction p with
  | nil => simp [mul, coeffOf]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rcases hp with ⟨hm, hrest⟩
      rw [show mul ((a, m) :: rest) q = mulMono a m q ++ mul rest q from rfl]
      rw [coeffOf_append, coeffOf_mulMono, ih hrest, Gauss.add_zero]
      cases hsub : subExp t m with
      | none => simp [factor, hsub]
      | some k =>
        have hk : k.nx ≠ 0 := by
          intro hk0
          have hx : t.nx = 0 := by
            have h := congrArg Mono.nx (mul_subExp hsub)
            simp only [Mono.mul, hm, hk0] at h
            simpa [Nat.zero_add] using h.symm
          exact ht hx
        simp [factor, hsub, coeff_listNxFree_zero hq hk, Gauss.mul_zero]

theorem coeff_slice_mul_gC (k : Nat) (f : Poly) (t : Mono) :
    coeffOf (sliceC (k + 2) (mul f gC)) t =
      coeffOf (sliceC k f ++ mul (sliceC (k + 2) f) gC0) t := by
  by_cases ht : t.c = 0
  · rw [coeff_sliceC]
    simp only [ht, ite_true]
    rw [gC_eq_split, mul_append_right_coeff, coeffOf_append, coeffOf_append]
    have hsq := coeff_slice_mul_cSq k f t
    rw [coeff_sliceC] at hsq
    simp only [ht, ite_true] at hsq
    have hfree := coeff_slice_mul_cFree (k + 2) f gC0 listCFree_gC0 t
    rw [coeff_sliceC] at hfree
    simp only [ht, ite_true] at hfree
    rw [hsq, hfree]
  · have h1 : coeffOf (sliceC k f) t = 0 := by rw [coeff_sliceC]; simp [ht]
    have h2 : coeffOf (mul (sliceC (k + 2) f) gC0) t = 0 :=
      listCFree_mul (sliceC_list_cFree _ _) listCFree_gC0 t ht
    rw [coeffOf_append, h1, h2, Gauss.zero_add, coeff_sliceC]
    simp [ht]

theorem coeff_slice_mul_gN (k : Nat) (f : Poly) (t : Mono) :
    coeffOf (sliceNx (k + 2) (mul f gN)) t =
      coeffOf (sliceNx k f ++ mul (sliceNx (k + 2) f) gN0) t := by
  by_cases ht : t.nx = 0
  · rw [coeff_sliceNx]
    simp only [ht, ite_true]
    rw [gN_eq_split, mul_append_right_coeff, coeffOf_append, coeffOf_append]
    have hsq := coeff_slice_mul_nxSq k f t
    rw [coeff_sliceNx] at hsq
    simp only [ht, ite_true] at hsq
    have hfree := coeff_slice_mul_nxFree (k + 2) f gN0 listNxFree_gN0 t
    rw [coeff_sliceNx] at hfree
    simp only [ht, ite_true] at hfree
    rw [hsq, hfree]
  · have h1 : coeffOf (sliceNx k f) t = 0 := by rw [coeff_sliceNx]; simp [ht]
    have h2 : coeffOf (mul (sliceNx (k + 2) f) gN0) t = 0 :=
      listNxFree_mul (sliceNx_list_nxFree _ _) listNxFree_gN0 t ht
    rw [coeffOf_append, h1, h2, Gauss.zero_add, coeff_sliceNx]
    simp [ht]

/-- Sbuccia solo `c²`. -/
def peelC : Poly → Option (Poly × Poly)
  | [] => none
  | (a, m) :: rest =>
    if a = 0 then
      match peelC rest with
      | none => none
      | some (rest', cof) => some ((a, m) :: rest', cof)
    else if _h : 2 ≤ m.c then
      let m' := shiftC m
      some ([(a, m'), (-a, shiftS m')] ++ rest, single a m')
    else
      match peelC rest with
      | none => none
      | some (rest', cof) => some ((a, m) :: rest', cof)

def cTerm (m : Mono) : Nat := 3 ^ m.c

def cWeight : Poly → Nat
  | [] => 0
  | (a, m) :: rest => (if a = 0 then 0 else cTerm m) + cWeight rest

theorem cWeight_zero_small {p : Poly} (h : cWeight p = 0) : cListSmall p := by
  induction p with
  | nil => simp [cListSmall]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      have hsum : (if a = 0 then 0 else cTerm m) + cWeight rest = 0 := by
        simpa [cWeight] using h
      have hrest : cWeight rest = 0 := by omega
      have ha : a = 0 := by
        by_cases hz : a = 0
        · exact hz
        · simp only [hz, ite_false] at hsum
          have hpos : 0 < cTerm m := by
            simpa [cTerm] using Nat.pow_pos (n := m.c) (by decide : 0 < 3)
          omega
      exact ⟨Or.inl ha, ih hrest⟩

theorem peelC_none_small {p : Poly} (h : peelC p = none) : cListSmall p := by
  induction p with
  | nil => simp [cListSmall]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      by_cases ha : a = 0
      · rw [peelC, ite_eq_left ha] at h
        cases hrest : peelC rest with
        | none => exact ⟨Or.inl ha, ih hrest⟩
        | some val => simp [hrest] at h
      · rw [peelC, ite_eq_right ha] at h
        by_cases hc : 2 ≤ m.c
        · rw [dite_eq_left hc] at h
          simp at h
        · rw [dite_eq_right hc] at h
          cases hrest : peelC rest with
          | none => exact ⟨Or.inr (Nat.lt_of_not_ge hc), ih hrest⟩
          | some val => simp [hrest] at h

theorem peelC_coeff (p : Poly) : ∀ rest cof, peelC p = some (rest, cof) → ∀ t,
    coeffOf p t = coeffOf (rest ++ mul cof gC) t := by
  induction p with
  | nil =>
    intro rest cof h t
    simp [peelC] at h
  | cons head tail ih =>
    intro rest cof h t
    cases head with
    | mk a m =>
      by_cases ha : a = 0
      · rw [peelC, ite_eq_left ha] at h
        cases htail : peelC tail with
        | none => simp [htail] at h
        | some val =>
          cases val with
          | mk rest' cof' =>
            simp only [htail] at h
            have hpair : ((a, m) :: rest', cof') = (rest, cof) := Option.some.inj h
            injection hpair with hr hc
            subst hr hc
            simp only [coeffOf, List.cons_append, coeffOf_append, ih rest' cof' htail t]
      · rw [peelC, ite_eq_right ha] at h
        by_cases hc : 2 ≤ m.c
        · rw [dite_eq_left hc] at h
          dsimp at h
          have hpair := Option.some.inj h
          injection hpair with hr hcof
          subst hr hcof
          rw [coeffOf, coeff_head_c a m hc t]
          exact coeffOf_rotate [(a, shiftC m), (-a, shiftS (shiftC m))] tail
            (mul (single a (shiftC m)) gC) t
        · rw [dite_eq_right hc] at h
          cases htail : peelC tail with
          | none => simp [htail] at h
          | some val =>
            cases val with
            | mk rest' cof' =>
              simp only [htail] at h
              have hpair : ((a, m) :: rest', cof') = (rest, cof) := Option.some.inj h
              injection hpair with hr hcof
              subst hr hcof
              simp only [coeffOf, List.cons_append, coeffOf_append, ih rest' cof' htail t]

theorem cWeight_step (c : Nat) (hc : 2 ≤ c) : 2 * 3 ^ (c - 2) < 3 ^ c := by
  have h9 : (3 : Nat) ^ 2 = 9 := by decide
  have wpos : 0 < 3 ^ (c - 2) := Nat.pow_pos (by decide)
  calc
    2 * 3 ^ (c - 2) < 9 * 3 ^ (c - 2) :=
      Nat.mul_lt_mul_of_pos_right (by decide : (2 : Nat) < 9) wpos
    _ = 3 ^ c := by
          rw [← h9, ← Nat.pow_add, Nat.add_comm 2 (c - 2), Nat.sub_add_cancel hc]

theorem peelC_weight (p : Poly) : ∀ rest cof, peelC p = some (rest, cof) →
    cWeight rest < cWeight p := by
  induction p with
  | nil =>
    intro rest cof h
    simp [peelC] at h
  | cons head tail ih =>
    intro rest cof h
    cases head with
    | mk a m =>
      by_cases ha : a = 0
      · rw [peelC, ite_eq_left ha] at h
        cases htail : peelC tail with
        | none => simp [htail] at h
        | some val =>
          cases val with
          | mk rest' cof' =>
            simp only [htail] at h
            have hpair : ((a, m) :: rest', cof') = (rest, cof) := Option.some.inj h
            injection hpair with hr _hc
            subst hr
            simpa [cWeight, ite_eq_left ha, Nat.zero_add] using ih rest' cof' htail
      · rw [peelC, ite_eq_right ha] at h
        by_cases hc : 2 ≤ m.c
        · rw [dite_eq_left hc] at h
          dsimp at h
          have hpair := Option.some.inj h
          injection hpair with hr _hcof
          subst hr
          simp only [cWeight, ite_eq_right ha, ite_eq_right (Gauss.neg_ne_zero ha), cTerm,
            shiftC, shiftS]
          rw [← Nat.add_assoc, ← Nat.two_mul]
          exact Nat.add_lt_add_right (cWeight_step m.c hc) (cWeight tail)
        · rw [dite_eq_right hc] at h
          cases htail : peelC tail with
          | none => simp [htail] at h
          | some val =>
            cases val with
            | mk rest' cof' =>
              simp only [htail] at h
              have hpair : ((a, m) :: rest', cof') = (rest, cof) := Option.some.inj h
              injection hpair with hr _hcof
              subst hr
              simp only [cWeight, ite_eq_right ha]
              exact Nat.add_lt_add_left (ih rest' cof' htail) (cTerm m)

structure CSplit where
  rem : Poly
  fc : Poly

def cAssemble (s : CSplit) : Poly := s.rem ++ mul s.fc gC

def pushC (s : CSplit) (cof : Poly) : CSplit := { s with fc := s.fc ++ cof }

/-- Coefficiente di `mul (p ++ q) r`. -/
theorem mul_append_left_coeff (p q r : Poly) (t : Mono) :
    coeffOf (mul (p ++ q) r) t = coeffOf (mul p r ++ mul q r) t := by
  induction p with
  | nil => simp [mul]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, mul, coeffOf_append, ih]
      rw [← Gauss.add_assoc, ← coeffOf_append]

theorem pushC_coeff (s : CSplit) (cof : Poly) (t : Mono) :
    coeffOf (cAssemble (pushC s cof)) t =
      coeffOf (cAssemble s) t + coeffOf (mul cof gC) t := by
  simp only [pushC, cAssemble]
  calc
    coeffOf (s.rem ++ mul (s.fc ++ cof) gC) t
        = coeffOf s.rem t + coeffOf (mul (s.fc ++ cof) gC) t := by rw [coeffOf_append]
    _ = coeffOf s.rem t + coeffOf (mul s.fc gC ++ mul cof gC) t := by
          rw [mul_append_left_coeff]
    _ = coeffOf s.rem t + (coeffOf (mul s.fc gC) t + coeffOf (mul cof gC) t) := by
          rw [coeffOf_append]
    _ = (coeffOf s.rem t + coeffOf (mul s.fc gC) t) + coeffOf (mul cof gC) t := by
          rw [Gauss.add_assoc]
    _ = coeffOf (s.rem ++ mul s.fc gC) t + coeffOf (mul cof gC) t := by
          rw [← coeffOf_append]

def reduceCAux : Nat → Poly → CSplit
  | 0, p => ⟨p, []⟩
  | fuel + 1, p =>
    match peelC p with
    | none => ⟨p, []⟩
    | some (rest, cof) => pushC (reduceCAux fuel rest) cof

def reduceC (p : Poly) : CSplit := reduceCAux (cWeight p) p

theorem reduceCAux_spec (fuel : Nat) (p : Poly) (h : cWeight p ≤ fuel) :
    cListSmall (reduceCAux fuel p).rem ∧
      ∀ t, coeffOf p t = coeffOf (cAssemble (reduceCAux fuel p)) t := by
  induction fuel generalizing p with
  | zero =>
    have hz : cWeight p = 0 := by omega
    refine ⟨cWeight_zero_small hz, ?_⟩
    intro t
    simp [reduceCAux, cAssemble, mul]
  | succ fuel ih =>
    cases hpeel : peelC p with
    | none =>
      have hred : reduceCAux (fuel + 1) p = ⟨p, []⟩ := by
        simp [reduceCAux, hpeel]
      rw [hred]
      refine ⟨peelC_none_small hpeel, ?_⟩
      intro t
      simp [cAssemble, mul]
    | some val =>
      cases val with
      | mk rest cof =>
        have hlt : cWeight rest < cWeight p := peelC_weight p rest cof hpeel
        have hle : cWeight rest ≤ fuel := by omega
        have ih' := ih rest hle
        refine ⟨?_, ?_⟩
        · simpa [reduceCAux, hpeel, pushC] using ih'.1
        · intro t
          simp only [reduceCAux, hpeel]
          rw [peelC_coeff p rest cof hpeel t, coeffOf_append, ih'.2 t]
          exact (pushC_coeff (reduceCAux fuel rest) cof t).symm

theorem reduceC_small (p : Poly) : cListSmall (reduceC p).rem :=
  (reduceCAux_spec (cWeight p) p (Nat.le_refl _)).1

theorem reduceC_sound (p : Poly) (t : Mono) :
    coeffOf p t = coeffOf (cAssemble (reduceC p)) t :=
  (reduceCAux_spec (cWeight p) p (Nat.le_refl _)).2 t

def arSq : Mono := {Mono.one with ar := 2}
def aiSq : Mono := {Mono.one with ai := 2}
def brSq : Mono := {Mono.one with br := 2}
def biSq : Mono := {Mono.one with bi := 2}

/-- `ar² + ai² + br² + bi²`. -/
def amp : Poly := single 1 arSq ++ single 1 aiSq ++ single 1 brSq ++ single 1 biSq

/-- `ar² + ai² + br² + bi² − 1`. Non è un generatore di `reduce`. -/
def gA : Poly := amp ++ single (-1) Mono.one

end Universe.Quotient
