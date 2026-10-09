/-
Collasso della serie, in forma algebrica.

`exp(-i φ a) = cos φ · 1 + (-i sin φ) · a` quando `a² = 1`.
I due membri sono serie formali: il coefficiente di `φ^n / n!` è confrontato
dopo aver tolto il fattoriale, che è lo stesso dai due lati. Non è un limite.

`cosCoeff` e `sinCoeff` sono i numeratori delle serie di coseno e seno:
`1, 0, -1, 0, 1, …` e `0, 1, 0, -1, 0, …`.
-/
import Universe.Ring

namespace Universe.Series

open Universe.Ring

def cosCoeff : Nat → Int
  | 0 => 1
  | 1 => 0
  | n + 2 => -cosCoeff n

def sinCoeff : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => -sinCoeff n

theorem cosCoeff_zero : cosCoeff 0 = 1 := rfl
theorem cosCoeff_one : cosCoeff 1 = 0 := rfl
theorem cosCoeff_succ_succ (n : Nat) : cosCoeff (n + 2) = -cosCoeff n := rfl

theorem sinCoeff_zero : sinCoeff 0 = 0 := rfl
theorem sinCoeff_one : sinCoeff 1 = 1 := rfl
theorem sinCoeff_succ_succ (n : Nat) : sinCoeff (n + 2) = -sinCoeff n := rfl

/-- Dinamica lineare con scalari di Gauss. Gli assiomi sono quelli usati dal collasso. -/
structure Dyn (M : Type) where
  mul : M → M → M
  add : M → M → M
  one : M
  zero : M
  smul : Gauss → M → M
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  add_zero : ∀ x, add x zero = x
  zero_add : ∀ x, add zero x = x
  smul_one : ∀ x, smul 1 x = x
  zero_smul : ∀ x, smul 0 x = zero
  smul_mul : ∀ z w x, smul (z * w) x = smul z (smul w x)
  smul_add : ∀ z x y, smul z (add x y) = add (smul z x) (smul z y)

def pow {M} (D : Dyn M) (a : M) : Nat → M
  | 0 => D.one
  | n + 1 => D.mul (pow D a n) a

theorem pow_zero {M} (D : Dyn M) (a : M) : pow D a 0 = D.one := rfl

theorem pow_succ {M} (D : Dyn M) (a : M) (n : Nat) :
    pow D a (n + 1) = D.mul (pow D a n) a := rfl

/-- Se `a² = 1`, allora `a^{n+2} = a^n`. -/
theorem pow_period {M} (D : Dyn M) (a : M) (ha : D.mul a a = D.one) (n : Nat) :
    pow D a (n + 2) = pow D a n := by
  rw [pow_succ, pow_succ, D.mul_assoc, ha, D.mul_one]

/-- `-i`, il generatore della fase. -/
def j : Gauss := -Gauss.i

theorem j_mul_j : j * j = -1 := by
  unfold j
  ext <;> simp <;> grind

theorem j_pow_two_step (n : Nat) : j ^ (n + 2) = -j ^ n := by
  rw [Gauss.pow_two_step, j_mul_j, Gauss.mul_neg_one]

/-- Coefficiente di `φ^n / n!` in `exp(-i φ a)`, senza il fattoriale. -/
def expSeries {M} (D : Dyn M) (a : M) (n : Nat) : M :=
  D.smul (j ^ n) (pow D a n)

/-- Coefficiente di `φ^n / n!` in `cos φ · 1 + (-i sin φ) · a`, senza il fattoriale. -/
def closedSeries {M} (D : Dyn M) (a : M) (n : Nat) : M :=
  D.add (D.smul (Gauss.ofInt (cosCoeff n)) D.one)
    (D.smul (j * Gauss.ofInt (sinCoeff n)) a)

theorem expCoeff {M} (D : Dyn M) (a : M) (ha : D.mul a a = D.one) (n : Nat) :
    expSeries D a n = closedSeries D a n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 =>
      simp only [expSeries, closedSeries, pow_zero, cosCoeff_zero, sinCoeff_zero]
      rw [Gauss.ofInt_one, Gauss.ofInt_zero, Gauss.mul_zero, D.zero_smul, D.add_zero]
      have hpow : j ^ (0 : Nat) = 1 := by simp [Gauss.pow_eq, Gauss.npow]
      rw [hpow, D.smul_one]
    | 1 =>
      simp only [expSeries, closedSeries, pow_succ, pow_zero, cosCoeff_one, sinCoeff_one]
      rw [Gauss.ofInt_zero, Gauss.ofInt_one, Gauss.mul_one, D.zero_smul, D.zero_add, D.one_mul]
      have hscal : j ^ (1 : Nat) = j := by
        simp only [Gauss.pow_eq]
        change (1 * j) = j
        exact Gauss.one_mul j
      rw [hscal]
    | n + 2 =>
      have ihn := ih n (by omega : n < n + 2)
      -- Il passo usa `a^{n+2} = a^n` e `(-i)^{n+2} = -(-i)^n`.
      have hpow : pow D a (n + 2) = pow D a n := pow_period D a ha n
      have hscal : j ^ (n + 2) = -j ^ n := j_pow_two_step n
      -- I numeratori di coseno e seno cambiano solo di segno ogni due gradi.
      have hc : Gauss.ofInt (cosCoeff (n + 2)) = -Gauss.ofInt (cosCoeff n) := by
        rw [cosCoeff_succ_succ, Gauss.ofInt_neg]
      have hs : Gauss.ofInt (sinCoeff (n + 2)) = -Gauss.ofInt (sinCoeff n) := by
        rw [sinCoeff_succ_succ, Gauss.ofInt_neg]
      have hcos : -1 * Gauss.ofInt (cosCoeff n) = Gauss.ofInt (cosCoeff (n + 2)) := by
        rw [Gauss.neg_one_mul, ← hc]
      -- `(-1) · (j · s) = j · (-s)`, perché `-1` commuta con `j`.
      have hsin : -1 * (j * Gauss.ofInt (sinCoeff n)) = j * Gauss.ofInt (sinCoeff (n + 2)) := by
        rw [← Gauss.mul_assoc, Gauss.mul_comm (-1) j, Gauss.mul_assoc, Gauss.neg_one_mul, ← hs]
      calc
        expSeries D a (n + 2)
            = D.smul (j ^ (n + 2)) (pow D a (n + 2)) := rfl
        _ = D.smul (-j ^ n) (pow D a n) := by rw [hscal, hpow]
        _ = D.smul (-1 * j ^ n) (pow D a n) := by rw [Gauss.neg_one_mul]
        _ = D.smul (-1) (D.smul (j ^ n) (pow D a n)) := by rw [D.smul_mul]
        _ = D.smul (-1) (expSeries D a n) := rfl
        _ = D.smul (-1) (closedSeries D a n) := by rw [ihn]
        _ = D.smul (-1)
              (D.add (D.smul (Gauss.ofInt (cosCoeff n)) D.one)
                (D.smul (j * Gauss.ofInt (sinCoeff n)) a)) := rfl
        _ = D.add (D.smul (-1) (D.smul (Gauss.ofInt (cosCoeff n)) D.one))
              (D.smul (-1) (D.smul (j * Gauss.ofInt (sinCoeff n)) a)) := by
                rw [D.smul_add]
        _ = D.add (D.smul (-1 * Gauss.ofInt (cosCoeff n)) D.one)
              (D.smul (-1 * (j * Gauss.ofInt (sinCoeff n))) a) := by
                rw [← D.smul_mul, ← D.smul_mul]
        _ = D.add (D.smul (Gauss.ofInt (cosCoeff (n + 2))) D.one)
              (D.smul (j * Gauss.ofInt (sinCoeff (n + 2))) a) := by
                rw [hcos, hsin]
        _ = closedSeries D a (n + 2) := rfl

/-- Le due serie formali coincidono su ogni grado. -/
theorem expSeries_eq_closed {M} (D : Dyn M) (a : M) (ha : D.mul a a = D.one) :
    expSeries D a = closedSeries D a := by
  funext n
  exact expCoeff D a ha n

end Universe.Series
