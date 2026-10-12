/-
Somme parziali del coseno e del seno, su un razionale.

`cTerm k x` è `cosCoeff k · xᵏ / k!`, `sTerm` il seno. `cosSum` e `sinSum`
li sommano fino a `N`. Non è un limite: per ogni grado `m` la convoluzione
di quei termini è il termine in `x + y`. La stessa forma, su `xᵏ / k!`,
è `exp_add`.

`sumTo_degree` taglia `n = k + (n − k)`. `sumTo_leibniz` ne ricava il passo
della convoluzione: lo usano il coseno, il seno e `exp`.

`C_N² + S_N² − 1` è la coda `tailSum`: i gradi `1 … N` si cancellano.
Il suo valore assoluto è al più `remainder`, la coda di `exp(2|x|)`.
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

/-- Il peso `k` si legge termine a termine, dopo lo spostamento dell'indice. -/
theorem sumTo_weight_of_pointwise (m : Nat) (conv prev : Nat → Rat) (z : Rat)
    (h : ∀ j, ((j + 1 : Nat) : Rat) * conv (j + 1) = z * prev j) :
    sumTo (m + 1) (fun k => (k : Rat) * conv k) = z * sumTo m prev := by
  rw [sumTo_weight_shift, ← sumTo_mul]
  exact sumTo_congr fun j _ => h j

/-- I due pesi `k` e `n − k` portano `x · F` e `y · F`: il grado porta `(x + y) · F`. -/
theorem sumTo_leibniz (m : Nat) (conv : Nat → Rat) (prev x y : Rat)
    (hweight : sumTo (m + 1) (fun k => (k : Rat) * conv k) = x * prev)
    (htail : sumTo (m + 1) (fun k => ((m + 1 - k : Nat) : Rat) * conv k) = y * prev) :
    ((m + 1 : Nat) : Rat) * sumTo (m + 1) conv = (x + y) * prev := by
  rw [sumTo_degree, sumTo_add, hweight, htail]
  grind

/-- Il passo `(m + 1) · conv = z · prev`, con `prev` già chiuso, dà il termine successivo. -/
theorem series_succ {m : Nat} {conv prev term next z : Rat}
    (hstep : ((m + 1 : Nat) : Rat) * conv = z * prev) (hprev : prev = term)
    (hderiv : z * term = ((m + 1 : Nat) : Rat) * next) : conv = next := by
  apply nat_mul_cancel (n := m + 1) (Nat.succ_ne_zero m)
  calc
    ((m + 1 : Nat) : Rat) * conv = z * prev := hstep
    _ = z * term := by rw [hprev]
    _ = ((m + 1 : Nat) : Rat) * next := hderiv

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
      -x * sumTo m (sinConvTerm x y m) :=
  sumTo_weight_of_pointwise m (fun k => cosConvTerm x y (m + 1) k)
    (fun j => sinConvTerm x y m j) (-x) <| by
      intro j
      unfold cosConvTerm sinConvTerm
      rw [Nat.succ_sub_succ]
      exact term_cos_weight j m x y

theorem sin_weight (m : Nat) (x y : Rat) :
    sumTo (m + 1) (fun k => (k : Rat) * sinConvTerm x y (m + 1) k) =
      x * sumTo m (cosConvTerm x y m) :=
  sumTo_weight_of_pointwise m (fun k => sinConvTerm x y (m + 1) k)
    (fun j => cosConvTerm x y m j) x <| by
      intro j
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
  rw [Rat.neg_add]
  exact sumTo_leibniz m (fun k => cosConvTerm x y (m + 1) k) (sumTo m (sinConvTerm x y m))
    (-x) (-y) (cos_weight m x y) (cos_tail m x y)

theorem sinConv_step (m : Nat) (x y : Rat) :
    ((m + 1 : Nat) : Rat) * sumTo (m + 1) (sinConvTerm x y (m + 1)) =
      (x + y) * sumTo m (cosConvTerm x y m) :=
  sumTo_leibniz m (fun k => sinConvTerm x y (m + 1) k) (sumTo m (cosConvTerm x y m))
    x y (sin_weight m x y) (sin_tail m x y)

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
    · exact series_succ (cosConv_step m x y) ihs (cTerm_deriv m (x + y)).symm
    · exact series_succ (sinConv_step m x y) ihc (sTerm_deriv m (x + y)).symm

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

/-- Termine `xᵐ / m!`. -/
def expTerm (m : Nat) (x : Rat) : Rat :=
  x ^ m / (fact m : Rat)

@[simp] theorem expTerm_zero (x : Rat) : expTerm 0 x = 1 := by
  unfold expTerm
  rw [fact_zero, Rat.pow_zero]
  grind

/-- `(m + 1) · expTerm (m + 1) x = x · expTerm m x`. -/
theorem expTerm_deriv (m : Nat) (x : Rat) :
    ((m + 1 : Nat) : Rat) * expTerm (m + 1) x = x * expTerm m x := by
  unfold expTerm
  rw [fact_succ m, Rat.natCast_mul, Rat.pow_succ, Rat.div_def, Rat.div_def]
  have hc : ((m + 1 : Nat) : Rat) ≠ 0 := by
    intro h
    exact Nat.succ_ne_zero m (Rat.natCast_eq_zero_iff.mp h)
  rw [scale_div _ _ _ hc]
  grind

/-- `expTerm k x · expTerm (n − k) y`. -/
def expConvTerm (x y : Rat) (n : Nat) : Nat → Rat :=
  fun k => expTerm k x * expTerm (n - k) y

theorem exp_point (j m : Nat) (x y : Rat) :
    ((j + 1 : Nat) : Rat) * expConvTerm x y (m + 1) (j + 1) =
      x * expConvTerm x y m j := by
  unfold expConvTerm
  rw [Nat.succ_sub_succ]
  have h := expTerm_deriv j x
  grind

theorem expConvTerm_rev (n k : Nat) (hk : k ≤ n) (x y : Rat) :
    expConvTerm x y n (n - k) = expConvTerm y x n k := by
  unfold expConvTerm
  rw [Nat.sub_sub_self hk]
  grind

theorem expConv_symm (n : Nat) (x y : Rat) :
    sumTo n (expConvTerm x y n) = sumTo n (expConvTerm y x n) :=
  sumTo_reflect fun k hk => expConvTerm_rev n k hk x y

theorem exp_weight (m : Nat) (x y : Rat) :
    sumTo (m + 1) (fun k => (k : Rat) * expConvTerm x y (m + 1) k) =
      x * sumTo m (expConvTerm x y m) :=
  sumTo_weight_of_pointwise m (expConvTerm x y (m + 1)) (expConvTerm x y m) x
    fun j => exp_point j m x y

theorem exp_tail (m : Nat) (x y : Rat) :
    sumTo (m + 1) (fun k => ((m + 1 - k : Nat) : Rat) * expConvTerm x y (m + 1) k) =
      y * sumTo m (expConvTerm x y m) := by
  rw [sumTo_reflect_weight fun k hk => expConvTerm_rev (m + 1) k hk x y, exp_weight,
    expConv_symm]

theorem expConv_step (m : Nat) (x y : Rat) :
    ((m + 1 : Nat) : Rat) * sumTo (m + 1) (expConvTerm x y (m + 1)) =
      (x + y) * sumTo m (expConvTerm x y m) :=
  sumTo_leibniz m (expConvTerm x y (m + 1)) (sumTo m (expConvTerm x y m)) x y
    (exp_weight m x y) (exp_tail m x y)

/-- `Σ_{k ≤ m} expTerm k x · expTerm (m − k) y = expTerm m (x + y)`. -/
theorem exp_add (m : Nat) (x y : Rat) :
    sumTo m (fun k => expTerm k x * expTerm (m - k) y) = expTerm m (x + y) := by
  induction m with
  | zero => simp [sumTo, Nat.sub_self, expTerm_zero, Rat.mul_one]
  | succ m ih =>
    exact series_succ (expConv_step m x y) ih (expTerm_deriv m (x + y)).symm

/-- `cₖ(−x) = cₖ(x)` e `sₖ(−x) = −sₖ(x)`. -/
theorem term_neg (k : Nat) (x : Rat) :
    cTerm k (-x) = cTerm k x ∧ sTerm k (-x) = -sTerm k x := by
  induction k with
  | zero =>
    constructor
    · simp
    · simp
  | succ k ih =>
    rcases ih with ⟨ihc, ihs⟩
    constructor
    · exact series_succ (cTerm_deriv k (-x)) ihs <| by
        rw [Rat.neg_neg, Rat.mul_neg, ← Rat.neg_mul]
        exact (cTerm_deriv k x).symm
    · exact series_succ (sTerm_deriv k (-x)) ihc <| by
        calc
          -x * cTerm k x = -(x * cTerm k x) := by rw [Rat.neg_mul]
          _ = -(((k + 1 : Nat) : Rat) * sTerm (k + 1) x) := by rw [← sTerm_deriv k x]
          _ = ((k + 1 : Nat) : Rat) * -sTerm (k + 1) x := by rw [← Rat.mul_neg]

/-- `cⱼ cₖ + sⱼ sₖ`. -/
def circleTerm (x : Rat) (j k : Nat) : Rat :=
  cTerm j x * cTerm k x + sTerm j x * sTerm k x

theorem diag_closed (m : Nat) (x : Rat) :
    sumTo m (fun k => circleTerm x k (m - k)) = cTerm m 0 := by
  have h := angle_add_cos m x (-x)
  rw [Rat.add_neg_cancel] at h
  rw [← h]
  refine sumTo_congr ?_
  intro k _
  unfold circleTerm
  rw [(term_neg (m - k) x).1, (term_neg (m - k) x).2]
  grind

theorem cTerm_at_zero (m : Nat) : cTerm m 0 = if m = 0 then 1 else 0 := by
  cases m with
  | zero => simp
  | succ m =>
    unfold cTerm
    rw [Rat.pow_succ, Rat.mul_zero, Rat.mul_zero, Rat.div_def, Rat.zero_mul]
    simp

/-- Somma da `lo` a `hi` compresi. Vuota se `hi < lo`. -/
def sumRange (lo hi : Nat) (f : Nat → Rat) : Rat :=
  if lo ≤ hi then sumTo (hi - lo) (fun i => f (lo + i)) else 0

theorem sumRange_of_le {lo hi : Nat} (h : lo ≤ hi) (f : Nat → Rat) :
    sumRange lo hi f = sumTo (hi - lo) (fun i => f (lo + i)) := by
  unfold sumRange
  split
  · rfl
  · rename_i hnot
    exact absurd h hnot

theorem sumRange_of_gt {lo hi : Nat} (h : hi < lo) (f : Nat → Rat) :
    sumRange lo hi f = 0 := by
  unfold sumRange
  split
  · rename_i hle
    exact absurd hle (Nat.not_le_of_gt h)
  · rfl

theorem sumRange_singleton (n : Nat) (f : Nat → Rat) : sumRange n n f = f n := by
  rw [sumRange_of_le (Nat.le_refl n), Nat.sub_self, sumTo, Nat.add_zero]

theorem sumRange_zero (n : Nat) (f : Nat → Rat) : sumRange 0 n f = sumTo n f := by
  rw [sumRange_of_le (Nat.zero_le n), Nat.sub_zero]
  simp

theorem sumRange_succ_hi {lo hi : Nat} (h : lo ≤ hi) (f : Nat → Rat) :
    sumRange lo (hi + 1) f = sumRange lo hi f + f (hi + 1) := by
  have h' : lo ≤ hi + 1 := Nat.le_trans h (Nat.le_succ hi)
  rw [sumRange_of_le h, sumRange_of_le h', Nat.succ_sub h, sumTo]
  refine congrArg (sumTo (hi - lo) (fun i => f (lo + i)) + ·) ?_
  have : lo + (hi - lo + 1) = hi + 1 := by omega
  simp [this]

theorem sumRange_succ_lo {lo hi : Nat} (h : lo ≤ hi) (f : Nat → Rat) :
    sumRange lo hi f = f lo + sumRange (lo + 1) hi f := by
  rw [sumRange_of_le h]
  cases hd : hi - lo with
  | zero =>
    have heq : hi = lo := by omega
    rw [heq, sumTo, Nat.add_zero, sumRange_of_gt (Nat.lt_succ_self lo), Rat.add_zero]
  | succ d =>
    rw [sumTo_succ_left]
    have hle : lo + 1 ≤ hi := by omega
    have hsub : hi - (lo + 1) = d := by omega
    rw [sumRange_of_le hle, hsub]
    refine congrArg (f lo + ·) ?_
    refine sumTo_congr ?_
    intro i _
    have : lo + (i + 1) = lo + 1 + i := by omega
    simp [this]

/-- `Σ_{i = a}^{b + d} = Σ_{i = a}^{b} + Σ_{i = b + 1}^{b + d}`, se `a ≤ b`. -/
theorem sumRange_append {a b : Nat} (hab : a ≤ b) (f : Nat → Rat) :
    ∀ d, sumRange a (b + d) f = sumRange a b f + sumRange (b + 1) (b + d) f := by
  intro d
  induction d with
  | zero =>
    rw [Nat.add_zero, sumRange_of_gt (Nat.lt_succ_self b), Rat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ]
    have ha : a ≤ b + d := Nat.le_trans hab (Nat.le_add_right b d)
    rw [sumRange_succ_hi ha f, ih, Rat.add_assoc]
    by_cases hd : d = 0
    · subst hd
      simp only [Nat.add_zero]
      rw [sumRange_of_gt (Nat.lt_succ_self b), sumRange_singleton, Rat.zero_add]
    · rw [← sumRange_succ_hi (show b + 1 ≤ b + d by omega)]

/-- Taglia in `b`, anche se `a = b + 1` e il primo pezzo è vuoto. -/
theorem sumRange_cut {a b c : Nat} (ha : a ≤ b + 1) (hc : b < c) (f : Nat → Rat) :
    sumRange a c f = sumRange a b f + sumRange (b + 1) c f := by
  by_cases hab : a ≤ b
  · have happ := sumRange_append hab f (c - b)
    have hup : b + (c - b) = c := by
      rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hc)]
    simpa [hup] using happ
  · have heq : a = b + 1 := by omega
    subst heq
    rw [sumRange_of_gt (Nat.lt_succ_self b), Rat.zero_add]

theorem sumRange_reindex (d a b : Nat) (f : Nat → Rat) :
    sumRange (a + d) (b + d) (fun m => f (m - d)) = sumRange a b f := by
  by_cases h : a ≤ b
  · rw [sumRange_of_le h, sumRange_of_le (Nat.add_le_add_right h d)]
    have hsub : b + d - (a + d) = b - a := by omega
    rw [hsub]
    refine sumTo_congr ?_
    intro i _
    have : a + d + i - d = a + i := by omega
    simp [this]
  · have h' : ¬ a + d ≤ b + d := by omega
    unfold sumRange
    simp [h, h']

theorem sumRange_add (lo hi : Nat) (f g : Nat → Rat) :
    sumRange lo hi (fun i => f i + g i) = sumRange lo hi f + sumRange lo hi g := by
  by_cases hle : lo ≤ hi
  · rw [sumRange_of_le hle, sumRange_of_le hle, sumRange_of_le hle, sumTo_add]
  · unfold sumRange
    simp [hle, Rat.zero_add]

theorem sumRange_congr {lo hi : Nat} {f g : Nat → Rat}
    (h : ∀ i, lo ≤ i → i ≤ hi → f i = g i) : sumRange lo hi f = sumRange lo hi g := by
  by_cases hle : lo ≤ hi
  · rw [sumRange_of_le hle, sumRange_of_le hle]
    refine sumTo_congr ?_
    intro i hi
    exact h (lo + i) (Nat.le_add_right lo i) (by omega)
  · unfold sumRange
    simp [hle]

/-- Allunga di un grado la fascia interna: il nuovo estremo basso e quello alto. -/
theorem inner_grow {n m : Nat} (hmn : n + 2 ≤ m) (hm : m ≤ n + n) (f : Nat → Nat → Rat) :
    sumRange (m - (n + 1)) (n + 1) (fun k => f k (m - k)) =
      f (m - (n + 1)) (n + 1) +
        sumRange (m - n) n (fun k => f k (m - k)) +
        f (n + 1) (m - (n + 1)) := by
  have hle : m - (n + 1) ≤ n := by omega
  have hnext : m - (n + 1) + 1 = m - n := by omega
  have hback : m - (m - (n + 1)) = n + 1 := Nat.sub_sub_self (by omega)
  have hhi := sumRange_succ_hi hle (fun k => f k (m - k))
  have hlow := sumRange_succ_lo hle (fun k => f k (m - k))
  rw [hhi, hlow, hnext, hback]

theorem sumTo_ends {n : Nat} (hn : 1 ≤ n) (f : Nat → Rat) :
    sumTo n f = f 0 + sumRange 1 (n - 1) f + f n := by
  have h0 : sumTo n f = f 0 + sumRange 1 n f := by
    rw [← sumRange_zero, sumRange_succ_lo (Nat.zero_le n)]
  by_cases h1 : n = 1
  · subst h1
    simp [h0, sumRange_singleton, sumRange_of_gt (by decide : (0 : Nat) < 1), Rat.add_zero]
  · have hmid : sumRange 1 n f = sumRange 1 (n - 1) f + f n := by
      have hs := sumRange_succ_hi (lo := 1) (hi := n - 1) (by omega) f
      have hup : n - 1 + 1 = n := by omega
      simpa [hup] using hs
    rw [h0, hmid, ← Rat.add_assoc]

theorem diag_ends {n : Nat} (hn : 1 ≤ n) (f : Nat → Nat → Rat) :
    sumTo (n + 1) (fun k => f k (n + 1 - k)) =
      f 0 (n + 1) + sumRange 1 n (fun k => f k (n + 1 - k)) + f (n + 1) 0 := by
  have h := sumTo_ends (n := n + 1) (by omega) (fun k => f k (n + 1 - k))
  simpa [Nat.sub_self (n + 1), show (n + 1) - 1 = n by omega] using h

/-- Rettangolo `0 … n` × `0 … n`. -/
def rect (n : Nat) (f : Nat → Nat → Rat) : Rat :=
  sumTo n fun j => sumTo n fun k => f j k

/-- Diagonali `m ≤ n`, complete. -/
def lowBand (n : Nat) (f : Nat → Nat → Rat) : Rat :=
  sumTo n fun m => sumTo m fun k => f k (m - k)

/-- Diagonali `n < m ≤ 2n`: `k` corre da `m − n` a `n`. -/
def highBand (n : Nat) (f : Nat → Nat → Rat) : Rat :=
  sumRange (n + 1) (2 * n) fun m => sumRange (m - n) n fun k => f k (m - k)

theorem rect_succ (n : Nat) (f : Nat → Nat → Rat) :
    rect (n + 1) f =
      rect n f + sumTo n (fun j => f j (n + 1)) +
        sumTo n (fun k => f (n + 1) k) + f (n + 1) (n + 1) := by
  unfold rect
  have h :
      sumTo (n + 1) (fun j => sumTo (n + 1) (fun k => f j k)) =
        sumTo n (fun j => sumTo n (fun k => f j k) + f j (n + 1)) +
          (sumTo n (fun k => f (n + 1) k) + f (n + 1) (n + 1)) := by
    rfl
  rw [h, sumTo_add]
  grind

theorem low_succ (n : Nat) (f : Nat → Nat → Rat) :
    lowBand (n + 1) f =
      lowBand n f + sumTo (n + 1) (fun k => f k (n + 1 - k)) := by
  unfold lowBand
  rfl

/-- I tre bordi nuovi, meno la diagonale `n + 1`, danno il passo della coda. -/
theorem sub_cancel_band (a b c d e f g p q : Rat) :
    b + c + d + (e + f) + g =
      a + b + (p + c + e) + (q + d + f) + g - (p + a + q) := by
  grind

theorem high_succ_pos (n : Nat) (hn : 1 ≤ n) (f : Nat → Nat → Rat) :
    highBand (n + 1) f =
      highBand n f + sumTo n (fun j => f j (n + 1)) +
        sumTo n (fun k => f (n + 1) k) + f (n + 1) (n + 1) -
          sumTo (n + 1) (fun k => f k (n + 1 - k)) := by
  have happ := sumRange_append (a := n + 1) (b := n + 1) (Nat.le_refl _)
    (fun m => sumRange (m - n) n fun k => f k (m - k)) (n - 1)
  have hup : (n + 1) + (n - 1) = 2 * n := by omega
  have hhighn : highBand n f =
      sumRange (n + 1) (n + 1) (fun m => sumRange (m - n) n fun k => f k (m - k)) +
        sumRange (n + 2) (2 * n) (fun m => sumRange (m - n) n fun k => f k (m - k)) := by
    simpa [highBand, hup] using happ
  have hinner : sumRange (n + 1) (n + 1)
      (fun m => sumRange (m - n) n fun k => f k (m - k)) =
      sumRange 1 n fun k => f k (n + 1 - k) := by
    rw [sumRange_singleton]
    have hsub : (n + 1) - n = 1 := by omega
    simp [hsub]
  have hdiag := diag_ends hn f
  have hpt := sumRange_congr (lo := n + 2) (hi := 2 * n)
    (f := fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k))
    (g := fun m =>
      f (m - (n + 1)) (n + 1) + sumRange (m - n) n (fun k => f k (m - k)) +
        f (n + 1) (m - (n + 1)))
    (fun m hm1 hm2 => inner_grow hm1 (by omega) f)
  have hreRow := sumRange_reindex (n + 1) 1 (n - 1) (fun t => f t (n + 1))
  have hreCol := sumRange_reindex (n + 1) 1 (n - 1) (fun t => f (n + 1) t)
  have hlo : 1 + (n + 1) = n + 2 := by omega
  have hhi : (n - 1) + (n + 1) = 2 * n := by omega
  have hmid : sumRange (n + 2) (2 * n)
      (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) =
      sumRange (n + 2) (2 * n) (fun m => sumRange (m - n) n fun k => f k (m - k)) +
        sumRange 1 (n - 1) (fun t => f t (n + 1)) +
        sumRange 1 (n - 1) (fun t => f (n + 1) t) := by
    rw [hpt, sumRange_add, sumRange_add]
    rw [hlo, hhi] at hreRow hreCol
    rw [hreRow, hreCol]
    grind
  have hcut := sumRange_cut (a := n + 2) (b := 2 * n) (c := 2 * n + 2) (by omega) (by omega)
    (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k))
  have htwo := sumRange_succ_hi (lo := 2 * n + 1) (hi := 2 * n + 1) (Nat.le_refl _)
    (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k))
  have hsucc : 2 * n + 1 + 1 = 2 * n + 2 := by omega
  have hwide : 2 * (n + 1) = 2 * n + 2 := by omega
  have htwo' : sumRange (2 * n + 1) (2 * n + 2)
      (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) =
      sumRange (2 * n + 1) (2 * n + 1)
        (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) +
      sumRange (2 * n + 2) (2 * n + 2)
        (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) := by
    have hsing :=
      sumRange_singleton (2 * n + 1 + 1)
        (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k))
    rw [← hsucc, htwo, ← hsing]
  have hhigh1 : highBand (n + 1) f =
      sumRange (n + 2) (2 * n)
        (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) +
      sumRange (2 * n + 1) (2 * n + 1)
        (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) +
      sumRange (2 * n + 2) (2 * n + 2)
        (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) := by
    rw [highBand, hwide, hcut, htwo', Rat.add_assoc]
  have htop : sumRange (2 * n + 1) (2 * n + 1)
      (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) =
      f n (n + 1) + f (n + 1) n := by
    rw [sumRange_singleton]
    have hlo' : (2 * n + 1) - (n + 1) = n := by omega
    have hpair := sumRange_succ_hi (lo := n) (hi := n) (Nat.le_refl _)
      (fun k => f k ((2 * n + 1) - k))
    rw [hlo', hpair, sumRange_singleton]
    have hk : (2 * n + 1) - n = n + 1 := by omega
    have hn1 : (2 * n + 1) - (n + 1) = n := by omega
    simp [hk, hn1]
  have hcorner : sumRange (2 * n + 2) (2 * n + 2)
      (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) =
      f (n + 1) (n + 1) := by
    rw [sumRange_singleton]
    have hlo' : (2 * n + 2) - (n + 1) = n + 1 := by omega
    simp [hlo', sumRange_singleton]
  have hrow := sumTo_ends hn (fun j => f j (n + 1))
  have hcol := sumTo_ends hn (fun k => f (n + 1) k)
  have hhigh : highBand n f =
      sumRange 1 n (fun k => f k (n + 1 - k)) +
        sumRange (n + 2) (2 * n) (fun m => sumRange (m - n) n fun k => f k (m - k)) := by
    rw [hhighn, hinner]
  calc
    highBand (n + 1) f =
        sumRange (n + 2) (2 * n)
          (fun m => sumRange (m - (n + 1)) (n + 1) fun k => f k (m - k)) +
        (f n (n + 1) + f (n + 1) n) + f (n + 1) (n + 1) := by
      rw [hhigh1, htop, hcorner]
    _ = sumRange (n + 2) (2 * n) (fun m => sumRange (m - n) n fun k => f k (m - k)) +
        sumRange 1 (n - 1) (fun t => f t (n + 1)) +
        sumRange 1 (n - 1) (fun t => f (n + 1) t) +
        (f n (n + 1) + f (n + 1) n) + f (n + 1) (n + 1) := by
      rw [hmid]
    _ = (sumRange 1 n (fun k => f k (n + 1 - k)) +
          sumRange (n + 2) (2 * n) (fun m => sumRange (m - n) n fun k => f k (m - k))) +
        (f 0 (n + 1) + sumRange 1 (n - 1) (fun t => f t (n + 1)) + f n (n + 1)) +
        (f (n + 1) 0 + sumRange 1 (n - 1) (fun t => f (n + 1) t) + f (n + 1) n) +
        f (n + 1) (n + 1) -
        (f 0 (n + 1) + sumRange 1 n (fun k => f k (n + 1 - k)) + f (n + 1) 0) := by
      exact sub_cancel_band
        (sumRange 1 n fun k => f k (n + 1 - k))
        (sumRange (n + 2) (2 * n) fun m => sumRange (m - n) n fun k => f k (m - k))
        (sumRange 1 (n - 1) fun t => f t (n + 1))
        (sumRange 1 (n - 1) fun t => f (n + 1) t)
        (f n (n + 1)) (f (n + 1) n) (f (n + 1) (n + 1))
        (f 0 (n + 1)) (f (n + 1) 0)
    _ = highBand n f + sumTo n (fun j => f j (n + 1)) +
        sumTo n (fun k => f (n + 1) k) + f (n + 1) (n + 1) -
          sumTo (n + 1) (fun k => f k (n + 1 - k)) := by
      rw [← hhigh, ← hrow, ← hcol, ← hdiag]

theorem high_succ (n : Nat) (f : Nat → Nat → Rat) :
    highBand (n + 1) f =
      highBand n f + sumTo n (fun j => f j (n + 1)) +
        sumTo n (fun k => f (n + 1) k) + f (n + 1) (n + 1) -
          sumTo (n + 1) (fun k => f k (n + 1 - k)) := by
  cases n with
  | zero =>
    have hhigh : highBand 1 f = f 1 1 := by
      unfold highBand
      rw [sumRange_singleton, sumRange_singleton]
    have hzero : highBand 0 f = 0 := by
      unfold highBand
      rw [sumRange_of_gt (by decide : (0 : Nat) < 1)]
    have hrow : sumTo 0 (fun j => f j 1) = f 0 1 := by simp [sumTo]
    have hcol : sumTo 0 (fun k => f 1 k) = f 1 0 := by simp [sumTo]
    have hdiag : sumTo 1 (fun k => f k (1 - k)) = f 0 1 + f 1 0 := by
      rw [sumTo, sumTo, Nat.sub_self]
    rw [hhigh, hzero, hrow, hcol, hdiag, Rat.sub_eq_add_neg, Rat.zero_add,
      Rat.add_comm (f 0 1 + f 1 0) (f 1 1), Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
  | succ n =>
    exact high_succ_pos (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) f

theorem rect_eq_bands (n : Nat) (f : Nat → Nat → Rat) :
    rect n f = lowBand n f + highBand n f := by
  induction n with
  | zero =>
    unfold rect lowBand highBand
    rw [sumRange_of_gt (by decide : (0 : Nat) < 1), Rat.add_zero]
    simp [sumTo, Nat.sub_self]
  | succ n ih =>
    rw [rect_succ, ih, low_succ, high_succ]
    grind

/-- `T_N(x) = Σ_{m = N + 1}^{2N} Σ_{k = m − N}^{N} (cₖ cₘ₋ₖ + sₖ sₘ₋ₖ)`. -/
def tailSum (n : Nat) (x : Rat) : Rat :=
  highBand n (circleTerm x)

theorem low_is_one (n : Nat) (x : Rat) : lowBand n (circleTerm x) = 1 := by
  unfold lowBand
  rw [sumTo_congr fun m _ => diag_closed m x]
  induction n with
  | zero => simp [sumTo, cTerm_at_zero]
  | succ n ih =>
    rw [sumTo, ih, cTerm_at_zero, ite_eq_right (Nat.succ_ne_zero n), Rat.add_zero]

theorem circle_square (n : Nat) (x : Rat) :
    cosSum n x * cosSum n x + sinSum n x * sinSum n x = rect n (circleTerm x) := by
  unfold cosSum sinSum rect circleTerm
  have hc : sumTo n (fun k => cTerm k x) * sumTo n (fun k => cTerm k x) =
      sumTo n fun j => sumTo n fun k => cTerm j x * cTerm k x := by
    rw [Rat.mul_comm, ← sumTo_mul]
    refine sumTo_congr ?_
    intro j _
    rw [Rat.mul_comm, ← sumTo_mul]
  have hs : sumTo n (fun k => sTerm k x) * sumTo n (fun k => sTerm k x) =
      sumTo n fun j => sumTo n fun k => sTerm j x * sTerm k x := by
    rw [Rat.mul_comm, ← sumTo_mul]
    refine sumTo_congr ?_
    intro j _
    rw [Rat.mul_comm, ← sumTo_mul]
  rw [hc, hs, ← sumTo_add]
  refine sumTo_congr ?_
  intro j _
  rw [← sumTo_add]

/-- `C_N(x)² + S_N(x)² − 1` è la coda oltre il grado `N`. -/
theorem circle_tail (n : Nat) (x : Rat) :
    cosSum n x * cosSum n x + sinSum n x * sinSum n x - 1 = tailSum n x := by
  unfold tailSum
  rw [circle_square, rect_eq_bands, low_is_one, Rat.add_comm, Rat.add_sub_cancel]

theorem neg_abs_le_self (a : Rat) : -a.abs ≤ a := by
  by_cases h : 0 ≤ a
  · rw [Rat.abs_of_nonneg h]
    exact Rat.le_trans (by simpa [Rat.neg_zero] using (Rat.neg_le_neg_iff.mpr h)) h
  · have ha : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp h)
    rw [Rat.abs_of_nonpos ha, Rat.neg_neg]
    exact Rat.le_refl

theorem self_le_abs (a : Rat) : a ≤ a.abs := by
  by_cases h : 0 ≤ a
  · rw [Rat.abs_of_nonneg h]
    exact Rat.le_refl
  · have ha : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp h)
    rw [Rat.abs_of_nonpos ha]
    exact Rat.le_trans ha (by simpa [Rat.neg_zero] using (Rat.neg_le_neg ha))

theorem abs_le_iff {a b : Rat} (_hb : 0 ≤ b) : a.abs ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  constructor
  · intro h
    exact ⟨Rat.le_trans (Rat.neg_le_neg h) (neg_abs_le_self a), Rat.le_trans (self_le_abs a) h⟩
  · intro h
    rcases h with ⟨h1, h2⟩
    by_cases ha : 0 ≤ a
    · rw [Rat.abs_of_nonneg ha]
      exact h2
    · have hneg : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp ha)
      rw [Rat.abs_of_nonpos hneg]
      exact Rat.neg_le_iff.mpr h1

theorem abs_add_le (a b : Rat) : (a + b).abs ≤ a.abs + b.abs := by
  have hneg : -(a.abs + b.abs) ≤ a + b := by
    have h := Lean.Grind.OrderedAdd.add_le_add (neg_abs_le_self a) (neg_abs_le_self b)
    simpa [Rat.neg_add] using h
  have hpos : a + b ≤ a.abs + b.abs := Lean.Grind.OrderedAdd.add_le_add (self_le_abs a) (self_le_abs b)
  exact (abs_le_iff (Rat.add_nonneg Rat.abs_nonneg Rat.abs_nonneg)).mpr ⟨hneg, hpos⟩

theorem abs_mul (a b : Rat) : (a * b).abs = a.abs * b.abs := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · rw [Rat.abs_of_nonneg ha, Rat.abs_of_nonneg hb, Rat.abs_of_nonneg (Rat.mul_nonneg ha hb)]
  · have hb' : b ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hb)
    have hnb : 0 ≤ -b := by simpa [Rat.neg_zero] using (Rat.neg_le_neg hb')
    have hprod : a * b ≤ 0 :=
      Rat.neg_le_neg_iff.mp <| by
        simpa [Rat.neg_zero, Rat.mul_neg] using Rat.mul_nonneg ha hnb
    rw [Rat.abs_of_nonneg ha, Rat.abs_of_nonpos hb', Rat.abs_of_nonpos hprod]
    exact (Rat.mul_neg a b).symm
  · have ha' : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp ha)
    have hna : 0 ≤ -a := by simpa [Rat.neg_zero] using (Rat.neg_le_neg ha')
    have hprod : a * b ≤ 0 :=
      Rat.neg_le_neg_iff.mp <| by
        simpa [Rat.neg_zero, Rat.neg_mul] using Rat.mul_nonneg hna hb
    rw [Rat.abs_of_nonpos ha', Rat.abs_of_nonneg hb, Rat.abs_of_nonpos hprod, Rat.mul_comm,
      Rat.mul_comm (-a)]
    exact (Rat.mul_neg b a).symm
  · have ha' : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp ha)
    have hb' : b ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hb)
    have hna : 0 ≤ -a := by simpa [Rat.neg_zero] using (Rat.neg_le_neg ha')
    have hnb : 0 ≤ -b := by simpa [Rat.neg_zero] using (Rat.neg_le_neg hb')
    have hprod : 0 ≤ a * b := by
      rw [← Rat.neg_neg (a * b), ← Rat.neg_mul, ← Rat.mul_neg]
      exact Rat.mul_nonneg hna hnb
    rw [Rat.abs_of_nonpos ha', Rat.abs_of_nonpos hb', Rat.abs_of_nonneg hprod, Rat.neg_mul,
      Rat.mul_neg, Rat.neg_neg]

theorem abs_pow (a : Rat) (n : Nat) : (a ^ n).abs = a.abs ^ n := by
  induction n with
  | zero =>
    simp [Rat.pow_zero]
    rw [Rat.abs_of_nonneg (Rat.le_of_lt (by decide : (0 : Rat) < 1))]
  | succ n ih =>
    rw [Rat.pow_succ, Rat.pow_succ, abs_mul, ih]

theorem fact_pos (n : Nat) : 0 < (fact n : Rat) :=
  Rat.natCast_pos.mpr (Nat.pos_of_ne_zero (fact_ne_zero n))

theorem cosCoeff_abs_le : ∀ k : Nat, (cosCoeff k : Rat).abs ≤ 1
  | 0 => by
    rw [cosCoeff_zero, Rat.intCast_one, Rat.abs_of_nonneg (Rat.le_of_lt (by decide : (0 : Rat) < 1))]
    exact Rat.le_refl
  | 1 => by
    rw [cosCoeff_one, Rat.intCast_zero, Rat.abs_zero]
    exact Rat.le_of_lt (by decide : (0 : Rat) < 1)
  | k + 2 => by
    rw [cosCoeff_succ_succ, Rat.intCast_neg, Rat.abs_neg]
    exact cosCoeff_abs_le k

theorem sinCoeff_abs_le : ∀ k : Nat, (sinCoeff k : Rat).abs ≤ 1
  | 0 => by
    rw [sinCoeff_zero, Rat.intCast_zero, Rat.abs_zero]
    exact Rat.le_of_lt (by decide : (0 : Rat) < 1)
  | 1 => by
    rw [sinCoeff_one, Rat.intCast_one, Rat.abs_of_nonneg (Rat.le_of_lt (by decide : (0 : Rat) < 1))]
    exact Rat.le_refl
  | k + 2 => by
    rw [sinCoeff_succ_succ, Rat.intCast_neg, Rat.abs_neg]
    exact sinCoeff_abs_le k

theorem cTerm_abs_le (k : Nat) (x : Rat) :
    (cTerm k x).abs ≤ x.abs ^ k / (fact k : Rat) := by
  unfold cTerm
  rw [Rat.div_def, abs_mul, abs_mul, abs_pow]
  have hinv : 0 ≤ ((fact k : Rat)⁻¹) :=
    Rat.le_of_lt (Rat.inv_pos.mpr (fact_pos k))
  rw [Rat.abs_of_nonneg hinv, Rat.div_def]
  have hrest : 0 ≤ x.abs ^ k * (fact k : Rat)⁻¹ :=
    Rat.mul_nonneg (Rat.pow_nonneg Rat.abs_nonneg) hinv
  have hmul := Rat.mul_le_mul_of_nonneg_right (cosCoeff_abs_le k) hrest
  rw [← Rat.mul_assoc, Rat.one_mul] at hmul
  exact hmul

theorem sTerm_abs_le (k : Nat) (x : Rat) :
    (sTerm k x).abs ≤ x.abs ^ k / (fact k : Rat) := by
  unfold sTerm
  rw [Rat.div_def, abs_mul, abs_mul, abs_pow]
  have hinv : 0 ≤ ((fact k : Rat)⁻¹) :=
    Rat.le_of_lt (Rat.inv_pos.mpr (fact_pos k))
  rw [Rat.abs_of_nonneg hinv, Rat.div_def]
  have hrest : 0 ≤ x.abs ^ k * (fact k : Rat)⁻¹ :=
    Rat.mul_nonneg (Rat.pow_nonneg Rat.abs_nonneg) hinv
  have hmul := Rat.mul_le_mul_of_nonneg_right (sinCoeff_abs_le k) hrest
  rw [← Rat.mul_assoc, Rat.one_mul] at hmul
  exact hmul

theorem div_mul_div (a b c d : Rat) : a / b * (c / d) = a * c / (b * d) := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  grind

theorem two_mul (y : Rat) : (2 : Rat) * y = y + y := by
  rw [show (2 : Rat) = (1 : Rat) + 1 from Rat.natCast_add 1 1, Rat.add_mul, Rat.one_mul]

theorem exp_binom (m : Nat) (y : Rat) :
    sumTo m (fun k => y ^ m / ((fact k * fact (m - k) : Nat) : Rat)) =
      expTerm m ((2 : Rat) * y) := by
  have hterm : ∀ k, k ≤ m →
      expTerm k y * expTerm (m - k) y =
        y ^ m / ((fact k * fact (m - k) : Nat) : Rat) := by
    intro k hk
    unfold expTerm
    rw [div_mul_div, ← Lean.Grind.Semiring.pow_add, Nat.add_sub_cancel' hk, ← Rat.natCast_mul]
  rw [show sumTo m (fun k => y ^ m / ((fact k * fact (m - k) : Nat) : Rat)) =
      sumTo m (fun k => expTerm k y * expTerm (m - k) y) by
        symm
        exact sumTo_congr hterm, exp_add, ← two_mul]

theorem odd_repr (k : Nat) (h : k % 2 = 1) : k = 2 * (k / 2) + 1 := by
  have := Nat.div_add_mod k 2
  omega

theorem even_repr (k : Nat) (h : k % 2 = 0) : k = 2 * (k / 2) := by
  have := Nat.div_add_mod k 2
  omega

theorem cosCoeff_odd : ∀ k, cosCoeff (2 * k + 1) = 0
  | 0 => cosCoeff_one
  | k + 1 => by
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega, cosCoeff_succ_succ, cosCoeff_odd k,
      Int.neg_zero]

theorem sinCoeff_even : ∀ k, sinCoeff (2 * k) = 0
  | 0 => sinCoeff_zero
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, sinCoeff_succ_succ, sinCoeff_even k, Int.neg_zero]

theorem cTerm_odd (k : Nat) (h : k % 2 = 1) (x : Rat) : cTerm k x = 0 := by
  unfold cTerm
  rw [odd_repr k h, cosCoeff_odd, Rat.intCast_zero, Rat.div_def, Rat.zero_mul, Rat.zero_mul]

theorem sTerm_even (k : Nat) (h : k % 2 = 0) (x : Rat) : sTerm k x = 0 := by
  unfold sTerm
  rw [even_repr k h, sinCoeff_even, Rat.intCast_zero, Rat.div_def, Rat.zero_mul, Rat.zero_mul]

theorem monomial_nonneg (m k : Nat) (x : Rat) :
    0 ≤ x.abs ^ m / ((fact k * fact (m - k) : Nat) : Rat) := by
  have hpos : 0 < fact k * fact (m - k) :=
    Nat.mul_pos (Nat.pos_of_ne_zero (fact_ne_zero k)) (Nat.pos_of_ne_zero (fact_ne_zero (m - k)))
  rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.pow_nonneg Rat.abs_nonneg)
    (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hpos)))

/-- Manca `mul_le_mul` a due fattori non negativi. -/
theorem mul_le_mul_of_nonneg {a b c d : Rat} (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : a ≤ b)
    (hcd : c ≤ d) : a * c ≤ b * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hab hc)
    (Rat.mul_le_mul_of_nonneg_left hcd (Rat.le_trans ha hab))

theorem half_abs_mul {a b : Rat} {j k : Nat} {x : Rat}
    (ha : a.abs ≤ x.abs ^ j / (fact j : Rat))
    (hb : b.abs ≤ x.abs ^ k / (fact k : Rat)) :
    (a * b).abs ≤ x.abs ^ (j + k) / ((fact j * fact k : Nat) : Rat) := by
  rw [abs_mul]
  refine Rat.le_trans (mul_le_mul_of_nonneg Rat.abs_nonneg Rat.abs_nonneg ha hb) ?_
  rw [div_mul_div, ← Lean.Grind.Semiring.pow_add, ← Rat.natCast_mul]
  exact Rat.le_refl

theorem dot_abs_le (j k : Nat) (x : Rat) :
    (circleTerm x j k).abs ≤ x.abs ^ (j + k) / ((fact j * fact k : Nat) : Rat) := by
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · unfold circleTerm
    rw [sTerm_even j hj x, sTerm_even k hk x, Rat.mul_zero, Rat.add_zero]
    exact half_abs_mul (cTerm_abs_le j x) (cTerm_abs_le k x)
  · unfold circleTerm
    rw [sTerm_even j hj x, cTerm_odd k hk x, Rat.mul_zero, Rat.zero_mul, Rat.add_zero,
      Rat.abs_zero]
    simpa [show j + k - j = k by omega] using monomial_nonneg (j + k) j x
  · unfold circleTerm
    rw [cTerm_odd j hj x, sTerm_even k hk x, Rat.zero_mul, Rat.mul_zero, Rat.add_zero,
      Rat.abs_zero]
    simpa [show j + k - j = k by omega] using monomial_nonneg (j + k) j x
  · unfold circleTerm
    rw [cTerm_odd j hj x, cTerm_odd k hk x, Rat.zero_mul, Rat.zero_add]
    exact half_abs_mul (sTerm_abs_le j x) (sTerm_abs_le k x)

theorem sumTo_abs_le (n : Nat) (f : Nat → Rat) :
    (sumTo n f).abs ≤ sumTo n fun k => (f k).abs := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo, sumTo]
    exact Rat.le_trans (abs_add_le _ _) (Lean.Grind.OrderedAdd.add_le_add ih Rat.le_refl)

theorem sumRange_abs_le (lo hi : Nat) (f : Nat → Rat) :
    (sumRange lo hi f).abs ≤ sumRange lo hi fun i => (f i).abs := by
  by_cases hle : lo ≤ hi
  · rw [sumRange_of_le hle, sumRange_of_le hle]
    exact sumTo_abs_le _ _
  · rw [sumRange_of_gt (Nat.lt_of_not_le hle), sumRange_of_gt (Nat.lt_of_not_le hle), Rat.abs_zero]
    exact Rat.le_refl

theorem sumTo_le_of {n : Nat} {f g : Nat → Rat} (h : ∀ k, k ≤ n → f k ≤ g k) :
    sumTo n f ≤ sumTo n g := by
  induction n with
  | zero => simpa [sumTo] using h 0 (Nat.le_refl _)
  | succ n ih =>
    rw [sumTo, sumTo]
    exact Lean.Grind.OrderedAdd.add_le_add (ih fun k hk => h k (Nat.le_succ_of_le hk)) (h (n + 1) (Nat.le_refl _))

theorem sumRange_le_of {lo hi : Nat} {f g : Nat → Rat}
    (h : ∀ i, lo ≤ i → i ≤ hi → f i ≤ g i) : sumRange lo hi f ≤ sumRange lo hi g := by
  by_cases hle : lo ≤ hi
  · rw [sumRange_of_le hle, sumRange_of_le hle]
    refine sumTo_le_of ?_
    intro i hi
    exact h (lo + i) (Nat.le_add_right lo i) (by omega)
  · rw [sumRange_of_gt (Nat.lt_of_not_le hle), sumRange_of_gt (Nat.lt_of_not_le hle)]
    exact Rat.le_refl

theorem sumTo_nonneg {n : Nat} {f : Nat → Rat} (h : ∀ k, k ≤ n → 0 ≤ f k) : 0 ≤ sumTo n f := by
  induction n with
  | zero => simpa [sumTo] using h 0 (Nat.le_refl _)
  | succ n ih =>
    rw [sumTo]
    exact Rat.add_nonneg (ih fun k hk => h k (Nat.le_succ_of_le hk)) (h (n + 1) (Nat.le_refl _))

theorem sumRange_nonneg {lo hi : Nat} {f : Nat → Rat}
    (h : ∀ i, lo ≤ i → i ≤ hi → 0 ≤ f i) : 0 ≤ sumRange lo hi f := by
  by_cases hle : lo ≤ hi
  · rw [sumRange_of_le hle]
    refine sumTo_nonneg ?_
    intro i hi
    exact h (lo + i) (Nat.le_add_right lo i) (by omega)
  · rw [sumRange_of_gt (Nat.lt_of_not_le hle)]
    exact Rat.le_refl

theorem sumTo_extend {n m : Nat} {f : Nat → Rat} (hn : n ≤ m)
    (hnn : ∀ k, n < k → k ≤ m → 0 ≤ f k) : sumTo n f ≤ sumTo m f := by
  induction m with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero hn
    subst this
    exact Rat.le_refl
  | succ m ih =>
    by_cases h : n = m + 1
    · subst h
      exact Rat.le_refl
    · have hn' : n ≤ m := by omega
      have ih' := ih hn' fun k hk1 hk2 => hnn k hk1 (Nat.le_succ_of_le hk2)
      have hlast : 0 ≤ f (m + 1) := hnn (m + 1) (by omega) (Nat.le_refl _)
      rw [sumTo]
      have hgrow : sumTo m f ≤ f (m + 1) + sumTo m f := by
        have := (Rat.add_le_add_right (c := sumTo m f)).mpr hlast
        simpa [Rat.zero_add] using this
      exact Rat.le_trans ih' (by rw [Rat.add_comm]; exact hgrow)

theorem sumTo_split_low {lo hi : Nat} (hlo : 0 < lo) (hhi : lo ≤ hi) (f : Nat → Rat) :
    sumTo hi f = sumRange 0 (lo - 1) f + sumRange lo hi f := by
  have hpred : lo - 1 + 1 = lo := Nat.sub_add_cancel hlo
  rw [← sumRange_zero]
  have hcut := sumRange_cut (a := 0) (b := lo - 1) (c := hi) (by omega) (by omega) f
  simpa [hpred] using hcut

theorem sumRange_le_sumTo {lo hi n : Nat} (hlo : lo ≤ hi) (hhi : hi ≤ n) {f : Nat → Rat}
    (hnn : ∀ k, k ≤ n → 0 ≤ f k) : sumRange lo hi f ≤ sumTo n f := by
  have hdrop : sumRange lo hi f ≤ sumTo hi f := by
    cases lo with
    | zero => simp [sumRange_zero]
    | succ lo =>
      have hsplit := sumTo_split_low (Nat.succ_pos lo) hlo f
      have hp : 0 ≤ sumRange 0 lo f :=
        sumRange_nonneg fun i _ hi2 =>
          hnn i (Nat.le_trans hi2 (Nat.le_trans (Nat.le_trans (Nat.le_succ lo) hlo) hhi))
      have : sumRange (lo + 1) hi f ≤ sumRange 0 lo f + sumRange (lo + 1) hi f := by
        have hle0 := (Rat.add_le_add_right (c := sumRange (lo + 1) hi f)).mpr hp
        simpa [Rat.zero_add] using hle0
      simpa [hsplit] using this
  have hrest : sumTo hi f ≤ sumTo n f :=
    sumTo_extend hhi fun k _ hk2 => hnn k hk2
  exact Rat.le_trans hdrop hrest

/-- `r_N(x) = Σ_{m = N + 1}^{2N} (2|x|)ᵐ / m!`. -/
def remainder (n : Nat) (x : Rat) : Rat :=
  sumRange (n + 1) (2 * n) fun m => expTerm m ((2 : Rat) * x.abs)

theorem inner_abs_le (n m : Nat) (x : Rat) (hn : n ≤ m) (hm : m ≤ n + n) :
    (sumRange (m - n) n fun k => circleTerm x k (m - k)).abs ≤
      expTerm m ((2 : Rat) * x.abs) := by
  refine Rat.le_trans (sumRange_abs_le (m - n) n fun k => circleTerm x k (m - k)) ?_
  have hpoint : sumRange (m - n) n (fun k => (circleTerm x k (m - k)).abs) ≤
      sumRange (m - n) n fun k =>
        x.abs ^ m / ((fact k * fact (m - k) : Nat) : Rat) :=
    sumRange_le_of fun k hk1 hk2 => by
      have hkm : k ≤ m := Nat.le_trans hk2 hn
      have hdot := dot_abs_le k (m - k) x
      simpa [Nat.add_sub_cancel' hkm] using hdot
  refine Rat.le_trans hpoint ?_
  have hfull : sumRange (m - n) n
      (fun k => x.abs ^ m / ((fact k * fact (m - k) : Nat) : Rat)) ≤
      sumTo m fun k => x.abs ^ m / ((fact k * fact (m - k) : Nat) : Rat) :=
    sumRange_le_sumTo (by omega) hn fun k _ => monomial_nonneg m k x
  refine Rat.le_trans hfull ?_
  rw [exp_binom]
  exact Rat.le_refl

theorem tail_abs_le (n : Nat) (x : Rat) : (tailSum n x).abs ≤ remainder n x := by
  unfold tailSum remainder highBand
  refine Rat.le_trans (sumRange_abs_le _ _ _) ?_
  refine sumRange_le_of ?_
  intro m hm1 hm2
  exact inner_abs_le n m x (by omega) (by omega)

/-- `|C_N(x)² + S_N(x)² − 1| ≤ r_N(x)`. -/
theorem circle_bound (n : Nat) (x : Rat) :
    (cosSum n x * cosSum n x + sinSum n x * sinSum n x - 1).abs ≤ remainder n x := by
  rw [circle_tail]
  exact tail_abs_le n x

/-- Il punto `φ = 1`, `N = 8`: quattro razionali, e la coda sta sotto il resto. -/
theorem circle_eight :
    cosSum 8 1 = (4357 : Rat) / 8064 ∧
      sinSum 8 1 = (4241 : Rat) / 5040 ∧
        cosSum 8 1 * cosSum 8 1 + sinSum 8 1 * sinSum 8 1 - 1 =
          -(6991 : Rat) / 1625702400 ∧
          remainder 8 1 = (373426 : Rat) / 212837625 := by
  decide_cbv

end Universe.Angle
