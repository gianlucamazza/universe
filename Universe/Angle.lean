/-
Somme parziali del coseno e del seno, su un razionale.

`cTerm k x` è `cosCoeff k · xᵏ / k!`, `sTerm` il seno. `cosSum` e `sinSum`
li sommano fino a `N`. Non è un limite: per ogni grado `m` la convoluzione
di quei termini è il termine in `x + y`.

`sumTo_degree` taglia `n = k + (n − k)`. La convoluzione di `exp` usa lo
stesso taglio.
-/
import Universe.Series

namespace Universe.Angle

open Universe.Series

/-- `k!`. Il nucleo di Lean 4.34 non ha `Nat.factorial`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)

theorem fact_zero : fact 0 = 1 := rfl

theorem fact_succ (n : Nat) : fact (n + 1) = fact n * (n + 1) := rfl

theorem fact_ne_zero (n : Nat) : fact n ≠ 0 := by
  induction n with
  | zero => exact Nat.one_ne_zero
  | succ n ih =>
    rw [fact_succ]
    exact Nat.mul_ne_zero ih (Nat.succ_ne_zero n)

/-- `cosCoeff (n + 1) = −sinCoeff n` e `sinCoeff (n + 1) = cosCoeff n`. -/
theorem coeff_shift (n : Nat) :
    cosCoeff (n + 1) = -sinCoeff n ∧ sinCoeff (n + 1) = cosCoeff n := by
  induction n with
  | zero =>
    constructor
    · rw [cosCoeff_one, sinCoeff_zero, Int.neg_zero]
    · rw [sinCoeff_one, cosCoeff_zero]
  | succ n ih =>
    rcases ih with ⟨hc, hs⟩
    constructor
    · rw [cosCoeff_succ_succ, hs]
    · rw [sinCoeff_succ_succ, hc]

/-- Termine `cosCoeff k · xᵏ / k!`. -/
def cTerm (k : Nat) (x : Rat) : Rat :=
  (cosCoeff k : Rat) * x ^ k / (fact k : Rat)

/-- Termine `sinCoeff k · xᵏ / k!`. -/
def sTerm (k : Nat) (x : Rat) : Rat :=
  (sinCoeff k : Rat) * x ^ k / (fact k : Rat)

@[simp] theorem cTerm_zero (x : Rat) : cTerm 0 x = 1 := by
  unfold cTerm
  rw [fact_zero, cosCoeff_zero, Rat.pow_zero]
  grind

@[simp] theorem sTerm_zero (x : Rat) : sTerm 0 x = 0 := by
  unfold sTerm
  rw [fact_zero, sinCoeff_zero, Rat.pow_zero]
  grind

/-- `Σ_{k ≤ n} f k`. -/
def sumTo : Nat → (Nat → Rat) → Rat
  | 0, f => f 0
  | n + 1, f => sumTo n f + f (n + 1)

/-- `C_N(x) = Σ_{k ≤ N} cTerm k x`. -/
def cosSum (n : Nat) (x : Rat) : Rat := sumTo n (fun k => cTerm k x)

/-- `S_N(x) = Σ_{k ≤ N} sTerm k x`. -/
def sinSum (n : Nat) (x : Rat) : Rat := sumTo n (fun k => sTerm k x)

theorem sumTo_congr {n : Nat} {f g : Nat → Rat} (h : ∀ k, k ≤ n → f k = g k) :
    sumTo n f = sumTo n g := by
  induction n with
  | zero =>
    simpa [sumTo] using h 0 (Nat.le_refl 0)
  | succ n ih =>
    rw [sumTo, sumTo, ih fun k hk => h k (Nat.le_succ_of_le hk),
      h (n + 1) (Nat.le_refl _)]

theorem sumTo_add (n : Nat) (f g : Nat → Rat) :
    sumTo n (fun k => f k + g k) = sumTo n f + sumTo n g := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo, ih]
    grind

theorem sumTo_mul (n : Nat) (a : Rat) (f : Nat → Rat) :
    sumTo n (fun k => a * f k) = a * sumTo n f := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo, ih]
    grind

/-- La somma `f 0 + f 1 + … + f (n + 1)` parte da `f 0` e sposta l'indice. -/
theorem sumTo_succ_left (n : Nat) (f : Nat → Rat) :
    sumTo (n + 1) f = f 0 + sumTo n (fun k => f (k + 1)) := by
  induction n with
  | zero =>
    simp [sumTo]
  | succ n ih =>
    rw [sumTo, ih, sumTo, Rat.add_assoc]

/-- `Σ_{k ≤ n} f (n − k) = Σ_{k ≤ n} f k`. -/
theorem sumTo_rev (n : Nat) (f : Nat → Rat) : sumTo n (fun k => f (n - k)) = sumTo n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo_succ_left]
    have hsub : ∀ k, (n + 1) - (k + 1) = n - k := fun k => Nat.succ_sub_succ n k
    simp only [Nat.sub_zero, hsub, ih, Rat.add_comm, sumTo]

/-- Se `F (n − k) = G k` per `k ≤ n`, le due somme coincidono. -/
theorem sumTo_reflect {n : Nat} {F G : Nat → Rat} (h : ∀ k, k ≤ n → F (n - k) = G k) :
    sumTo n F = sumTo n G := by
  rw [← sumTo_rev n F]
  exact sumTo_congr h

/-- Il peso `n − k` diventa `k` quando l'indice si riflette. -/
theorem sumTo_reflect_weight {n : Nat} {F G : Nat → Rat} (h : ∀ k, k ≤ n → F (n - k) = G k) :
    sumTo n (fun k => ((n - k : Nat) : Rat) * F k) = sumTo n (fun k => (k : Rat) * G k) := by
  refine sumTo_reflect ?_
  intro k hk
  rw [Nat.sub_sub_self hk, h k hk]

/-- Dentro la somma, `n = k + (n − k)`. -/
theorem sumTo_degree (n : Nat) (f : Nat → Rat) :
    (n : Rat) * sumTo n f =
      sumTo n (fun k => (k : Rat) * f k + ((n - k : Nat) : Rat) * f k) := by
  rw [← sumTo_mul]
  refine sumTo_congr ?_
  intro k hk
  have hnat : (n : Rat) = (k : Rat) + ((n - k : Nat) : Rat) := by
    rw [← Rat.natCast_add, Nat.add_sub_cancel' hk]
  rw [hnat, Rat.add_mul]

/-- Il peso `k` in `k = 0` è zero: la somma parte da `1` e l'indice scende di uno. -/
theorem sumTo_weight_shift (n : Nat) (f : Nat → Rat) :
    sumTo (n + 1) (fun k => (k : Rat) * f k) =
      sumTo n (fun k => ((k + 1 : Nat) : Rat) * f (k + 1)) := by
  rw [sumTo_succ_left]
  simp [Rat.zero_mul, Rat.zero_add]

theorem nat_mul_cancel {n : Nat} {a b : Rat} (hn : n ≠ 0)
    (h : (n : Rat) * a = (n : Rat) * b) : a = b := by
  have hz : (n : Rat) ≠ 0 := by simpa [Rat.natCast_eq_zero_iff] using hn
  have h' := congrArg ((n : Rat)⁻¹ * ·) h
  rw [← Rat.mul_assoc, ← Rat.mul_assoc, Rat.inv_mul_cancel _ hz, Rat.one_mul, Rat.one_mul] at h'
  exact h'

/-- `c · (a · (f · c)⁻¹) = a · f⁻¹` quando `c ≠ 0`. `grind` lascia aperto il caso `c = 0`. -/
theorem scale_div (a c f : Rat) (hc : c ≠ 0) : c * (a * (f * c)⁻¹) = a * f⁻¹ := by
  rw [Rat.inv_mul_rev]
  calc
    c * (a * (c⁻¹ * f⁻¹)) = a * c * (c⁻¹ * f⁻¹) := by rw [← Rat.mul_assoc, Rat.mul_comm c a]
    _ = a * (c * (c⁻¹ * f⁻¹)) := by rw [Rat.mul_assoc]
    _ = a * ((c * c⁻¹) * f⁻¹) := by rw [← Rat.mul_assoc c c⁻¹ f⁻¹]
    _ = a * (1 * f⁻¹) := by rw [Rat.mul_inv_cancel _ hc]
    _ = a * f⁻¹ := by rw [Rat.one_mul]

/-- `(m + 1) · cTerm (m + 1) x = −x · sTerm m x`. -/
theorem cTerm_deriv (m : Nat) (x : Rat) :
    ((m + 1 : Nat) : Rat) * cTerm (m + 1) x = -x * sTerm m x := by
  unfold cTerm sTerm
  rw [(coeff_shift m).1, fact_succ m, Rat.intCast_neg, Rat.natCast_mul, Rat.pow_succ, Rat.div_def,
    Rat.div_def]
  have hc : ((m + 1 : Nat) : Rat) ≠ 0 := by
    intro h
    exact Nat.succ_ne_zero m (Rat.natCast_eq_zero_iff.mp h)
  rw [scale_div _ _ _ hc]
  have hnum :
      -(sinCoeff m : Rat) * (x ^ m * x) = -x * ((sinCoeff m : Rat) * x ^ m) := by
    grind
  rw [hnum, Rat.mul_assoc]

/-- `(m + 1) · sTerm (m + 1) x = x · cTerm m x`. -/
theorem sTerm_deriv (m : Nat) (x : Rat) :
    ((m + 1 : Nat) : Rat) * sTerm (m + 1) x = x * cTerm m x := by
  unfold cTerm sTerm
  rw [(coeff_shift m).2, fact_succ m, Rat.natCast_mul, Rat.pow_succ, Rat.div_def, Rat.div_def]
  have hc : ((m + 1 : Nat) : Rat) ≠ 0 := by
    intro h
    exact Nat.succ_ne_zero m (Rat.natCast_eq_zero_iff.mp h)
  rw [scale_div _ _ _ hc]
  have hnum : (cosCoeff m : Rat) * (x ^ m * x) = x * ((cosCoeff m : Rat) * x ^ m) := by
    grind
  rw [hnum, Rat.mul_assoc]

/-- `cₖ(x) cₙ₋ₖ(y) − sₖ(x) sₙ₋ₖ(y)`. -/
def cosConvTerm (x y : Rat) (n : Nat) : Nat → Rat :=
  fun k => cTerm k x * cTerm (n - k) y - sTerm k x * sTerm (n - k) y

/-- `sₖ(x) cₙ₋ₖ(y) + cₖ(x) sₙ₋ₖ(y)`. -/
def sinConvTerm (x y : Rat) (n : Nat) : Nat → Rat :=
  fun k => sTerm k x * cTerm (n - k) y + cTerm k x * sTerm (n - k) y

theorem cosConvTerm_rev (n k : Nat) (hk : k ≤ n) (x y : Rat) :
    cosConvTerm x y n (n - k) = cosConvTerm y x n k := by
  unfold cosConvTerm
  rw [Nat.sub_sub_self hk]
  grind

theorem sinConvTerm_rev (n k : Nat) (hk : k ≤ n) (x y : Rat) :
    sinConvTerm x y n (n - k) = sinConvTerm y x n k := by
  unfold sinConvTerm
  rw [Nat.sub_sub_self hk]
  grind

theorem cosConv_symm (n : Nat) (x y : Rat) :
    sumTo n (cosConvTerm x y n) = sumTo n (cosConvTerm y x n) :=
  sumTo_reflect fun k hk => cosConvTerm_rev n k hk x y

theorem sinConv_symm (n : Nat) (x y : Rat) :
    sumTo n (sinConvTerm x y n) = sumTo n (sinConvTerm y x n) :=
  sumTo_reflect fun k hk => sinConvTerm_rev n k hk x y

theorem term_cos_weight (j m : Nat) (x y : Rat) :
    ((j + 1 : Nat) : Rat) *
        (cTerm (j + 1) x * cTerm (m - j) y - sTerm (j + 1) x * sTerm (m - j) y) =
      -x * (sTerm j x * cTerm (m - j) y + cTerm j x * sTerm (m - j) y) := by
  have hc := cTerm_deriv j x
  have hs := sTerm_deriv j x
  grind

theorem term_sin_weight (j m : Nat) (x y : Rat) :
    ((j + 1 : Nat) : Rat) *
        (sTerm (j + 1) x * cTerm (m - j) y + cTerm (j + 1) x * sTerm (m - j) y) =
      x * (cTerm j x * cTerm (m - j) y - sTerm j x * sTerm (m - j) y) := by
  have hc := cTerm_deriv j x
  have hs := sTerm_deriv j x
  grind

theorem cos_weight (m : Nat) (x y : Rat) :
    sumTo (m + 1) (fun k => (k : Rat) * cosConvTerm x y (m + 1) k) =
      -x * sumTo m (sinConvTerm x y m) := by
  rw [sumTo_weight_shift, ← sumTo_mul]
  refine sumTo_congr ?_
  intro j _
  unfold cosConvTerm sinConvTerm
  rw [Nat.succ_sub_succ]
  exact term_cos_weight j m x y

theorem sin_weight (m : Nat) (x y : Rat) :
    sumTo (m + 1) (fun k => (k : Rat) * sinConvTerm x y (m + 1) k) =
      x * sumTo m (cosConvTerm x y m) := by
  rw [sumTo_weight_shift, ← sumTo_mul]
  refine sumTo_congr ?_
  intro j _
  unfold sinConvTerm cosConvTerm
  rw [Nat.succ_sub_succ]
  exact term_sin_weight j m x y

theorem cos_tail (m : Nat) (x y : Rat) :
    sumTo (m + 1) (fun k => ((m + 1 - k : Nat) : Rat) * cosConvTerm x y (m + 1) k) =
      -y * sumTo m (sinConvTerm x y m) := by
  rw [sumTo_reflect_weight fun k hk => cosConvTerm_rev (m + 1) k hk x y, cos_weight, sinConv_symm]

theorem sin_tail (m : Nat) (x y : Rat) :
    sumTo (m + 1) (fun k => ((m + 1 - k : Nat) : Rat) * sinConvTerm x y (m + 1) k) =
      y * sumTo m (cosConvTerm x y m) := by
  rw [sumTo_reflect_weight fun k hk => sinConvTerm_rev (m + 1) k hk x y, sin_weight, cosConv_symm]

theorem cosConv_step (m : Nat) (x y : Rat) :
    ((m + 1 : Nat) : Rat) * sumTo (m + 1) (cosConvTerm x y (m + 1)) =
      -(x + y) * sumTo m (sinConvTerm x y m) := by
  rw [sumTo_degree, sumTo_add, cos_weight, cos_tail]
  grind

theorem sinConv_step (m : Nat) (x y : Rat) :
    ((m + 1 : Nat) : Rat) * sumTo (m + 1) (sinConvTerm x y (m + 1)) =
      (x + y) * sumTo m (cosConvTerm x y m) := by
  rw [sumTo_degree, sumTo_add, sin_weight, sin_tail]
  grind

theorem angle_add (m : Nat) (x y : Rat) :
    sumTo m (cosConvTerm x y m) = cTerm m (x + y) ∧
      sumTo m (sinConvTerm x y m) = sTerm m (x + y) := by
  induction m with
  | zero =>
    constructor
    · simp [sumTo, cosConvTerm, Nat.sub_self, cTerm_zero, sTerm_zero]
      grind
    · simp [sumTo, sinConvTerm, Nat.sub_self, cTerm_zero, sTerm_zero]
      grind
  | succ m ih =>
    rcases ih with ⟨ihc, ihs⟩
    constructor
    · apply nat_mul_cancel (n := m + 1) (Nat.succ_ne_zero m)
      calc
        ((m + 1 : Nat) : Rat) * sumTo (m + 1) (cosConvTerm x y (m + 1))
            = -(x + y) * sumTo m (sinConvTerm x y m) := cosConv_step m x y
        _ = -(x + y) * sTerm m (x + y) := by rw [ihs]
        _ = ((m + 1 : Nat) : Rat) * cTerm (m + 1) (x + y) := (cTerm_deriv m (x + y)).symm
    · apply nat_mul_cancel (n := m + 1) (Nat.succ_ne_zero m)
      calc
        ((m + 1 : Nat) : Rat) * sumTo (m + 1) (sinConvTerm x y (m + 1))
            = (x + y) * sumTo m (cosConvTerm x y m) := sinConv_step m x y
        _ = (x + y) * cTerm m (x + y) := by rw [ihc]
        _ = ((m + 1 : Nat) : Rat) * sTerm (m + 1) (x + y) := (sTerm_deriv m (x + y)).symm

/-- A grado `m`, `Σ_{k ≤ m} (cₖ(x) cₘ₋ₖ(y) − sₖ(x) sₘ₋ₖ(y)) = cₘ(x + y)`. -/
theorem angle_add_cos (m : Nat) (x y : Rat) :
    sumTo m (fun k => cTerm k x * cTerm (m - k) y - sTerm k x * sTerm (m - k) y) =
      cTerm m (x + y) := by
  have h := (angle_add m x y).1
  unfold cosConvTerm at h
  exact h

/-- A grado `m`, `Σ_{k ≤ m} (sₖ(x) cₘ₋ₖ(y) + cₖ(x) sₘ₋ₖ(y)) = sₘ(x + y)`. -/
theorem angle_add_sin (m : Nat) (x y : Rat) :
    sumTo m (fun k => sTerm k x * cTerm (m - k) y + cTerm k x * sTerm (m - k) y) =
      sTerm m (x + y) := by
  have h := (angle_add m x y).2
  unfold sinConvTerm at h
  exact h

end Universe.Angle
