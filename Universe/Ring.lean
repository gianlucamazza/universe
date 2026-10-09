/-
Razionali di Gauss: `a + b i` con `a`, `b` razionali.

È lo scalare del kernel Python (`universe.ring.Gauss`). Le leggi d'anello e
`i² = -1` sono teoremi: servono alle potenze di `-i` nella serie di `exp`.
-/
import Init.Data.Rat.Lemmas

namespace Universe.Ring

@[ext]
structure Gauss where
  re : Rat
  im : Rat
  deriving DecidableEq, Repr

namespace Gauss

instance : Zero Gauss where
  zero := ⟨0, 0⟩

instance : One Gauss where
  one := ⟨1, 0⟩

instance {n : Nat} : OfNat Gauss n where
  ofNat := ⟨(n : Rat), 0⟩

instance : Add Gauss where
  add z w := ⟨z.re + w.re, z.im + w.im⟩

instance : Neg Gauss where
  neg z := ⟨-z.re, -z.im⟩

instance : Sub Gauss where
  sub z w := ⟨z.re - w.re, z.im - w.im⟩

instance : Mul Gauss where
  mul z w := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def conj (z : Gauss) : Gauss :=
  ⟨z.re, -z.im⟩

/-- Unità immaginaria. -/
def i : Gauss :=
  ⟨0, 1⟩

def ofInt (n : Int) : Gauss :=
  ⟨(n : Rat), 0⟩

def npow : Nat → Gauss → Gauss
  | 0, _ => 1
  | n + 1, z => npow n z * z

instance : HPow Gauss Nat Gauss where
  hPow z n := npow n z

@[simp] theorem re_add (z w : Gauss) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : Gauss) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_sub (z w : Gauss) : (z - w).re = z.re - w.re := rfl
@[simp] theorem im_sub (z w : Gauss) : (z - w).im = z.im - w.im := rfl
@[simp] theorem re_neg (z : Gauss) : (-z).re = -z.re := rfl
@[simp] theorem im_neg (z : Gauss) : (-z).im = -z.im := rfl
@[simp] theorem re_mul (z w : Gauss) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem im_mul (z w : Gauss) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem re_i : i.re = 0 := rfl
@[simp] theorem im_i : i.im = 1 := rfl
@[simp] theorem re_zero : (0 : Gauss).re = 0 := rfl
@[simp] theorem im_zero : (0 : Gauss).im = 0 := rfl
@[simp] theorem re_one : (1 : Gauss).re = 1 := rfl
@[simp] theorem im_one : (1 : Gauss).im = 0 := rfl
@[simp] theorem re_two : (2 : Gauss).re = 2 := rfl
@[simp] theorem im_two : (2 : Gauss).im = 0 := rfl
@[simp] theorem re_ofInt (n : Int) : (ofInt n).re = n := rfl
@[simp] theorem im_ofInt (n : Int) : (ofInt n).im = 0 := rfl
@[simp] theorem pow_eq (z : Gauss) (n : Nat) : z ^ n = npow n z := rfl

theorem add_assoc (a b c : Gauss) : a + b + c = a + (b + c) := by
  ext <;> simp <;> grind

theorem add_comm (a b : Gauss) : a + b = b + a := by
  ext <;> simp <;> grind

theorem add_zero (a : Gauss) : a + 0 = a := by
  ext <;> simp <;> grind

theorem zero_add (a : Gauss) : 0 + a = a := by
  ext <;> simp <;> grind

theorem mul_assoc (a b c : Gauss) : a * b * c = a * (b * c) := by
  ext <;> simp <;> grind

theorem mul_comm (a b : Gauss) : a * b = b * a := by
  ext <;> simp <;> grind

theorem mul_one (a : Gauss) : a * 1 = a := by
  ext <;> simp <;> grind

theorem one_mul (a : Gauss) : 1 * a = a := by
  ext <;> simp <;> grind

theorem mul_zero (a : Gauss) : a * 0 = 0 := by
  ext <;> simp <;> grind

theorem zero_mul (a : Gauss) : 0 * a = 0 := by
  ext <;> simp <;> grind

theorem mul_add (a b c : Gauss) : a * (b + c) = a * b + a * c := by
  ext <;> simp <;> grind

theorem add_mul (a b c : Gauss) : (a + b) * c = a * c + b * c := by
  ext <;> simp <;> grind

/-- Sentinella del prodotto, la stessa della sezione «Calcolo» del kernel Python. -/
theorem one_add_i_mul_one_sub_i : (1 + i) * (1 - i) = (2 : Gauss) := by
  ext <;> simp <;> grind

theorem i_mul_i : i * i = -1 := by
  ext <;> simp <;> grind

theorem i_sq : i ^ (2 : Nat) = -1 := by
  simp only [pow_eq]
  change (1 * i) * i = -1
  rw [one_mul, i_mul_i]

theorem conj_i : conj i = -i := by
  ext <;> simp [conj] <;> grind

theorem ofInt_zero : ofInt 0 = 0 := by
  ext <;> simp <;> grind

theorem ofInt_one : ofInt 1 = 1 := by
  ext <;> simp <;> grind

theorem ofInt_neg_one : ofInt (-1) = -1 := by
  ext <;> simp <;> grind

theorem ofInt_neg (n : Int) : ofInt (-n) = -ofInt n := by
  ext <;> simp <;> grind

theorem ofInt_mul (m n : Int) : ofInt (m * n) = ofInt m * ofInt n := by
  ext <;> simp <;> grind

theorem pow_two_step (z : Gauss) (n : Nat) : z ^ (n + 2) = z ^ n * (z * z) := by
  simp only [pow_eq]
  show npow n z * z * z = npow n z * (z * z)
  rw [mul_assoc]

theorem mul_neg_one (z : Gauss) : z * -1 = -z := by
  ext <;> simp <;> grind

theorem neg_one_mul (z : Gauss) : -1 * z = -z := by
  ext <;> simp <;> grind

theorem add_neg_cancel (z : Gauss) : z + -z = 0 := by
  ext <;> simp <;> grind

theorem neg_add_cancel (z : Gauss) : -z + z = 0 := by
  ext <;> simp <;> grind

theorem neg_neg (z : Gauss) : - -z = z := by
  ext <;> simp <;> grind

end Gauss

end Universe.Ring
