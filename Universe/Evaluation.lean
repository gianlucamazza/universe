/-
Valutazione nel punto.

`evalAt` è un omomorfismo: rispetta `polySame`, il prodotto e il coniugio.
`eval_polySame` dice che due polinomi con gli stessi coefficienti hanno lo
stesso valore. `eval_pmul` e `eval_conj` portano prodotto e coniugio sui
valori di Gauss. `eval_scale` porta la scala, `eval_const` una costante.
`evalAt2` sostituisce anche `c2` e `s2`. `evalAt2_pmul` è il prodotto.
Su un polinomio senza quegli esponenti, `evalAt2_agrees` coincide con `evalAt`.
`evalAt3` sostituisce anche `mx`, `my`, `mz`. `evalAt3_pmul` è il prodotto.
Su un polinomio senza quegli esponenti, `evalAt3_agrees` coincide con `evalAt2`.
`listEval` somma i coefficienti lungo un supporto senza ripetizioni;
`eval_cover` lo identifica con `evalAt`. Lungo `n = e_x`, `eval_gN_axis_x`
azzera `gN` e `eval_bracket_axis_x` legge `⟨0|U|0⟩ = c`.
`eval_bracket_axis_x_1` legge `⟨1|U|0⟩ = −i s`. `eval_columnBorn` porta
il modulo sul valore, e `born_axis_x` ne ricava i pesi `c²` e `s²`.
Se `(c, s)` sta sul cerchio, `eval_gC_on_circle` azzera `gC`.
-/
import Universe.Epistemology

namespace Universe.Evaluation

open Universe.Ring
open Universe.Quotient hiding mul
open Universe.Dynamics
open Universe.Epistemology

/-- Immagine di un coefficiente sotto `c, s, nx, ny, nz`. -/
def monoImage (c s nx ny nz : Rat) (z : Gauss) (m : Mono) : Gauss :=
  ⟨z.re * monoVal c s nx ny nz m, z.im * monoVal c s nx ny nz m⟩

theorem monoImage_add (c s nx ny nz : Rat) (x y : Gauss) (m : Mono) :
    monoImage c s nx ny nz (x + y) m =
      monoImage c s nx ny nz x m + monoImage c s nx ny nz y m := by
  simp only [monoImage, Gauss.re_add, Gauss.im_add]
  ext <;> simp <;> grind

theorem monoImage_zero (c s nx ny nz : Rat) (m : Mono) :
    monoImage c s nx ny nz 0 m = 0 := by
  simp only [monoImage]
  ext <;> simp <;> grind

/-- Somma `coeff(p, m) · valore(m)` lungo una lista di monomi. -/
def listEval (c s nx ny nz : Rat) (p : Poly) : List Mono → Gauss
  | [] => 0
  | m :: ms => monoImage c s nx ny nz (coeffOf p m) m + listEval c s nx ny nz p ms

theorem listEval_congr {p q : Poly} (c s nx ny nz : Rat) (ms : List Mono)
    (h : ∀ m, m ∈ ms → coeffOf p m = coeffOf q m) :
    listEval c s nx ny nz p ms = listEval c s nx ny nz q ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [listEval, listEval, h m List.mem_cons_self]
    rw [ih (fun n hn => h n (List.mem_cons_of_mem m hn))]

theorem listEval_extra (c s nx ny nz : Rat) (p : Poly) (ms : List Mono)
    (h : ∀ m, m ∈ ms → coeffOf p m = 0) :
    listEval c s nx ny nz p ms = 0 := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [listEval, h m List.mem_cons_self, monoImage_zero, Gauss.zero_add]
    exact ih (fun n hn => h n (List.mem_cons_of_mem m hn))

theorem listEval_cons_hit (c s nx ny nz : Rat) (a : Gauss) (mono : Mono) (rest : Poly)
    (ms : List Mono) (hnd : ms.Nodup) (hm : mono ∈ ms) :
    listEval c s nx ny nz ((a, mono) :: rest) ms =
      monoImage c s nx ny nz a mono + listEval c s nx ny nz rest ms := by
  induction ms with
  | nil => cases hm
  | cons n ns ih =>
    rw [List.nodup_cons] at hnd
    rw [listEval]
    by_cases hn : n = mono
    · subst hn
      have htail : listEval c s nx ny nz ((a, n) :: rest) ns =
          listEval c s nx ny nz rest ns := by
        apply listEval_congr
        intro n' hn'
        have hne : n ≠ n' := fun he => hnd.1 (he ▸ hn')
        simp only [coeffOf, ite_eq_right hne, Gauss.zero_add]
      rw [htail]
      have hc : coeffOf ((a, n) :: rest) n = a + coeffOf rest n := by
        simp only [coeffOf, ite_true]
      rw [hc, monoImage_add, Gauss.add_assoc, listEval]
    · have hm' : mono ∈ ns := by
        cases hm with
        | head => exact absurd rfl hn
        | tail _ hmem => exact hmem
      have hc : coeffOf ((a, mono) :: rest) n = coeffOf rest n := by
        simp only [coeffOf, ite_eq_right (Ne.symm hn), Gauss.zero_add]
      rw [hc, ih hnd.2 hm', ← Gauss.add_assoc,
        Gauss.add_comm (monoImage c s nx ny nz (coeffOf rest n) n), Gauss.add_assoc, listEval]

theorem eval_cover (c s nx ny nz : Rat) (p : Poly) :
    ∀ ms, ms.Nodup → (∀ m, m ∈ support p → m ∈ ms) →
      evalAt c s nx ny nz p = listEval c s nx ny nz p ms := by
  induction p with
  | nil =>
    intro ms _ _
    rw [show evalAt c s nx ny nz ([] : Poly) = 0 from rfl]
    exact (listEval_extra c s nx ny nz [] ms (fun _ _ => rfl)).symm
  | cons head rest ih =>
    cases head with
    | mk a n =>
      intro ms hnd hcover
      rw [show evalAt c s nx ny nz ((a, n) :: rest) =
        monoImage c s nx ny nz a n + evalAt c s nx ny nz rest from rfl]
      have hrest : ∀ m, m ∈ support rest → m ∈ ms := by
        intro m hm
        exact hcover m ((mem_support_cons a n rest m).2 (Or.inr hm))
      rw [ih ms hnd hrest]
      have hn : n ∈ ms := hcover n ((mem_support_cons a n rest n).2 (Or.inl rfl))
      exact (listEval_cons_hit c s nx ny nz a n rest ms hnd hn).symm

/-- Due polinomi con gli stessi coefficienti hanno lo stesso valore nel punto. -/
theorem eval_polySame {p q : Poly} (h : polySame p q) (c s nx ny nz : Rat) :
    evalAt c s nx ny nz p = evalAt c s nx ny nz q := by
  let ms := support (p ++ q)
  have hnd : ms.Nodup := support_nodup (p ++ q)
  have hp := eval_cover c s nx ny nz p ms hnd
    (fun m hm => (mem_support_append p q m).2 (Or.inl hm))
  have hq := eval_cover c s nx ny nz q ms hnd
    (fun m hm => (mem_support_append p q m).2 (Or.inr hm))
  have hsame : listEval c s nx ny nz p ms = listEval c s nx ny nz q ms :=
    listEval_congr c s nx ny nz ms (fun m _ => h m)
  exact hp.trans (hsame.trans hq.symm)

theorem powR_add (z : Rat) (a b : Nat) : powR z (a + b) = powR z a * powR z b := by
  induction b with
  | zero => simp [powR]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 from Nat.add_succ a b, powR, ih, powR, Rat.mul_assoc]

theorem monoVal_mul (c s nx ny nz : Rat) (m n : Mono) :
    monoVal c s nx ny nz (m.mul n) = monoVal c s nx ny nz m * monoVal c s nx ny nz n := by
  simp only [monoVal, Mono.mul, powR_add]
  grind

theorem monoImage_mul (c s nx ny nz : Rat) (a b : Gauss) (m n : Mono) :
    monoImage c s nx ny nz (a * b) (m.mul n) =
      monoImage c s nx ny nz a m * monoImage c s nx ny nz b n := by
  simp only [monoImage, monoVal_mul, Gauss.re_mul, Gauss.im_mul]
  ext <;> simp <;> grind

theorem eval_mulMono (c s nx ny nz : Rat) (a : Gauss) (m : Mono) (q : Poly) :
    evalAt c s nx ny nz (mulMono a m q) =
      monoImage c s nx ny nz a m * evalAt c s nx ny nz q := by
  induction q with
  | nil => simp [mulMono, evalAt, Gauss.mul_zero]
  | cons head rest ih =>
    cases head with
    | mk b n =>
      simp only [mulMono, evalAt, ih, monoImage, monoVal_mul, Gauss.mul_add, Gauss.re_mul,
        Gauss.im_mul]
      ext <;> simp <;> grind

theorem eval_pmul (c s nx ny nz : Rat) (p q : Poly) :
    evalAt c s nx ny nz (pmul p q) = evalAt c s nx ny nz p * evalAt c s nx ny nz q := by
  induction p with
  | nil => simp [pmul, Universe.Quotient.mul, evalAt, Gauss.zero_mul]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show pmul ((a, m) :: rest) q = mulMono a m q ++ pmul rest q from rfl, eval_append,
        eval_mulMono, ih]
      rw [show evalAt c s nx ny nz ((a, m) :: rest) =
        monoImage c s nx ny nz a m + evalAt c s nx ny nz rest from rfl, Gauss.add_mul]

theorem conj_monoImage (c s nx ny nz : Rat) (a : Gauss) (m : Mono) :
    Gauss.conj (monoImage c s nx ny nz a m) = monoImage c s nx ny nz (Gauss.conj a) m := by
  simp only [monoImage, Gauss.conj]
  ext <;> simp <;> grind

theorem eval_conj (c s nx ny nz : Rat) (p : Poly) :
    evalAt c s nx ny nz (conjP p) = Gauss.conj (evalAt c s nx ny nz p) := by
  induction p with
  | nil => simp [conjP, evalAt, conj_zero]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show conjP ((a, m) :: rest) = (Gauss.conj a, m) :: conjP rest from rfl]
      rw [show evalAt c s nx ny nz ((Gauss.conj a, m) :: conjP rest) =
            monoImage c s nx ny nz (Gauss.conj a) m + evalAt c s nx ny nz (conjP rest) from rfl,
        ih, ← conj_monoImage,
        show evalAt c s nx ny nz ((a, m) :: rest) =
            monoImage c s nx ny nz a m + evalAt c s nx ny nz rest from rfl,
        conj_add]

theorem eval_pneg (c s nx ny nz : Rat) (p : Poly) :
    evalAt c s nx ny nz (pneg p) = -evalAt c s nx ny nz p := by
  induction p with
  | nil =>
    simp [pneg, evalAt]
    ext <;> simp
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show pneg ((a, m) :: rest) = (-a, m) :: pneg rest from rfl, evalAt, ih]
      rw [show evalAt c s nx ny nz ((a, m) :: rest) =
        ⟨a.re * monoVal c s nx ny nz m, a.im * monoVal c s nx ny nz m⟩ +
          evalAt c s nx ny nz rest from rfl]
      ext <;> simp <;> grind

theorem eval_psub (c s nx ny nz : Rat) (p q : Poly) :
    evalAt c s nx ny nz (psub p q) = evalAt c s nx ny nz p + -evalAt c s nx ny nz q := by
  rw [psub, eval_append, eval_pneg]

theorem gauss_of_sub (a b : Gauss) (h : a + -b = 0) : a = b := by
  calc
    a = a + 0 := (Gauss.add_zero a).symm
    _ = a + (-b + b) := by rw [Gauss.neg_add_cancel]
    _ = a + -b + b := (Gauss.add_assoc a (-b) b).symm
    _ = 0 + b := by rw [h]
    _ = b := Gauss.zero_add b

theorem eval_inIdeal {p : Poly} (hp : inIdeal p) (c s nx ny nz : Rat)
    (hc : evalAt c s nx ny nz gC = 0) (hn : evalAt c s nx ny nz gN = 0) :
    evalAt c s nx ny nz p = 0 := by
  rcases hp with ⟨fc, fn, h⟩
  have hs : polySame p (pmul fc gC ++ pmul fn gN) := h
  calc
    evalAt c s nx ny nz p = evalAt c s nx ny nz (pmul fc gC ++ pmul fn gN) :=
      eval_polySame hs c s nx ny nz
    _ = evalAt c s nx ny nz (pmul fc gC) + evalAt c s nx ny nz (pmul fn gN) :=
      eval_append c s nx ny nz _ _
    _ = evalAt c s nx ny nz fc * evalAt c s nx ny nz gC +
          evalAt c s nx ny nz fn * evalAt c s nx ny nz gN := by
        rw [eval_pmul, eval_pmul]
    _ = evalAt c s nx ny nz fc * 0 + evalAt c s nx ny nz fn * 0 := by rw [hc, hn]
    _ = 0 := by rw [Gauss.mul_zero, Gauss.mul_zero, Gauss.add_zero]

/-- `|z γ|² = |z|² |γ|²`. -/
theorem columnBorn_phase (z : Gauss) (p : Poly) :
    columnBorn (scale z p) = scale (z * Gauss.conj z) (columnBorn p) := by
  rw [columnBorn, conj_scale, ← scale_pmul_left]
  rw [scale_pmul_right (Gauss.conj z) p (conjP p), ← scale_mul_gauss]
  rfl

/-- Se `|z|² = 1`, la fase esce da ogni peso di Born. -/
theorem columnBorn_unit_phase (z : Gauss) (p : Poly) (hz : z * Gauss.conj z = 1) :
    columnBorn (scale z p) = columnBorn p := by
  rw [columnBorn_phase, hz, scale_one]

theorem spec_scale (keep : Mono → Option Mono) (z : Gauss) (p : Poly) :
    specPoly keep (scale z p) = scale z (specPoly keep p) := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [scale, specPoly]
      cases keep m with
      | none => exact ih
      | some k => simp only [scale, ih]

/-- Il monomio `1` vale `1` per ogni sostituzione. -/
theorem monoVal_one (c s nx ny nz : Rat) : monoVal c s nx ny nz Mono.one = 1 := by
  simp [monoVal, powR]

/-- Una costante non dipende da `c, s, n`. -/
theorem eval_const (c s nx ny nz : Rat) (a : Gauss) :
    evalAt c s nx ny nz (single a Mono.one) = a := by
  rw [eval_single, monoVal_one]
  ext <;> simp

/-- `eval` porta la scala di Gauss sul valore. -/
theorem eval_scale (c s nx ny nz : Rat) (z : Gauss) (p : Poly) :
    evalAt c s nx ny nz (scale z p) = z * evalAt c s nx ny nz p := by
  induction p with
  | nil =>
    simp [scale, evalAt]
    rw [Gauss.mul_zero]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show scale z ((a, m) :: rest) = (z * a, m) :: scale z rest from rfl]
      rw [show evalAt c s nx ny nz ((z * a, m) :: scale z rest) =
        ⟨(z * a).re * monoVal c s nx ny nz m, (z * a).im * monoVal c s nx ny nz m⟩ +
          evalAt c s nx ny nz (scale z rest) from rfl, ih]
      rw [show evalAt c s nx ny nz ((a, m) :: rest) =
        ⟨a.re * monoVal c s nx ny nz m, a.im * monoVal c s nx ny nz m⟩ +
          evalAt c s nx ny nz rest from rfl, Gauss.mul_add]
      have hterm :
          ⟨(z * a).re * monoVal c s nx ny nz m, (z * a).im * monoVal c s nx ny nz m⟩ =
            z * ⟨a.re * monoVal c s nx ny nz m, a.im * monoVal c s nx ny nz m⟩ := by
        ext <;> simp [Gauss.re_mul, Gauss.im_mul] <;> grind
      rw [hterm]

/-- `|z|²` di una costante è la costante `z · conj(z)`. -/
theorem columnBorn_const (z : Gauss) :
    columnBorn (single z Mono.one) = single (z * Gauss.conj z) Mono.one ++ [] := by
  rw [columnBorn, show conjP (single z Mono.one) = single (Gauss.conj z) Mono.one from rfl,
    pmul_single_single]
  rw [show Mono.one.mul Mono.one = Mono.one by ext <;> rfl]

/-- Valore di `|z|²` quando `z` è una costante. -/
theorem eval_column_const (c s nx ny nz : Rat) (z : Gauss) :
    evalAt c s nx ny nz (columnBorn (single z Mono.one)) = z * Gauss.conj z := by
  rw [columnBorn_const, eval_append, eval_const]
  simp [evalAt, Gauss.add_zero]

/-- `|z|²` valutato è il modulo del valore. -/
theorem eval_columnBorn (c s nx ny nz : Rat) (p : Poly) :
    evalAt c s nx ny nz (columnBorn p) =
      evalAt c s nx ny nz p * Gauss.conj (evalAt c s nx ny nz p) := by
  rw [columnBorn, eval_pmul, eval_conj]

/-- Lungo `e_x` i coefficienti di `gN` valgono zero, per ogni `c, s`. -/
theorem eval_gN_axis_x (c s : Rat) : evalAt c s 1 0 0 gN = 0 := by
  rw [gN, eval_append, eval_append, eval_append, eval_single, eval_single, eval_single,
    eval_single]
  simp [monoVal, powR, nxSq, nySq, nzSq]
  ext <;> simp <;> grind

/-- Sul cerchio, lungo qualunque asse, `gC` vale zero. -/
theorem eval_gC_on_circle (c s : Rat) (h : c * c + s * s = 1) :
    evalAt c s 1 0 0 gC = 0 := by
  rw [gC, eval_append, eval_append, eval_single, eval_single, eval_single]
  simp [monoVal, powR, cSq, sSq]
  ext <;> simp <;> grind

section
open Universe.Qubit

/-- Lungo `e_x`, `⟨0|U|0⟩` vale `c`: il termine `s nz` si annulla. -/
theorem eval_bracket_axis_x (c s : Rat) : evalAt c s 1 0 0 evolution.a00 = ⟨c, 0⟩ := by
  rw [evolution_a00_bin, eval_append, eval_single, eval_single]
  simp [monoVal, powR, c1, s1, nz1, Mono.mul, Gauss.re_neg, Gauss.im_neg, Gauss.re_i, Gauss.im_i]
  ext <;> simp <;> grind

/-- Lungo `e_x`, `⟨1|U|0⟩` vale `−i s`: il termine `s ny` si annulla. -/
theorem eval_bracket_axis_x_1 (c s : Rat) : evalAt c s 1 0 0 evolution.a10 = ⟨0, -s⟩ := by
  rw [evolution_a10_bin, eval_append, eval_single, eval_single]
  simp [monoVal, powR, s1, nx1, ny1, Mono.mul, Gauss.re_neg, Gauss.im_neg, Gauss.re_i,
    Gauss.im_i]
  ext <;> simp <;> grind

/-- Lungo `e_x`, i pesi di Born delle due ampiezze di `U` sono `c²` e `s²`. -/
theorem born_axis_x (c s : Rat) :
    evalAt c s 1 0 0 (columnBorn evolution.a00) = ⟨c * c, 0⟩ ∧
      evalAt c s 1 0 0 (columnBorn evolution.a10) = ⟨s * s, 0⟩ := by
  refine ⟨?_, ?_⟩
  · rw [eval_columnBorn, eval_bracket_axis_x]
    ext <;> simp [Gauss.conj] <;> grind
  · rw [eval_columnBorn, eval_bracket_axis_x_1]
    ext <;> simp [Gauss.conj] <;> grind

end

/-! ### Sostituzione di `c2` e `s2` -/

/-- Valore di un monomio, con anche `c2` e `s2`. -/
def monoVal2 (c s nx ny nz c2 s2 : Rat) (m : Mono) : Rat :=
  monoVal c s nx ny nz m * powR c2 m.c2 * powR s2 m.s2

/-- Immagine di un coefficiente sotto `c, s, n, c2, s2`. -/
def monoImage2 (c s nx ny nz c2 s2 : Rat) (z : Gauss) (m : Mono) : Gauss :=
  ⟨z.re * monoVal2 c s nx ny nz c2 s2 m, z.im * monoVal2 c s nx ny nz c2 s2 m⟩

/-- Valuta un polinomio sostituendo anche `c2` e `s2`. `evalAt` li ignora. -/
def evalAt2 (c s nx ny nz c2 s2 : Rat) : Poly → Gauss
  | [] => 0
  | (a, m) :: rest =>
      monoImage2 c s nx ny nz c2 s2 a m + evalAt2 c s nx ny nz c2 s2 rest

theorem monoVal2_mul (c s nx ny nz c2 s2 : Rat) (m n : Mono) :
    monoVal2 c s nx ny nz c2 s2 (m.mul n) =
      monoVal2 c s nx ny nz c2 s2 m * monoVal2 c s nx ny nz c2 s2 n := by
  simp only [monoVal2, monoVal, Mono.mul, powR_add]
  grind

theorem monoVal2_silent (c s nx ny nz c2 s2 : Rat) (m : Mono)
    (h : m.c2 = 0 ∧ m.s2 = 0) :
    monoVal2 c s nx ny nz c2 s2 m = monoVal c s nx ny nz m := by
  simp [monoVal2, h.1, h.2, powR]

theorem monoImage2_mul (c s nx ny nz c2 s2 : Rat) (a b : Gauss) (m n : Mono) :
    monoImage2 c s nx ny nz c2 s2 (a * b) (m.mul n) =
      monoImage2 c s nx ny nz c2 s2 a m * monoImage2 c s nx ny nz c2 s2 b n := by
  simp only [monoImage2, monoVal2_mul, Gauss.re_mul, Gauss.im_mul]
  ext <;> simp <;> grind

theorem evalAt2_append (c s nx ny nz c2 s2 : Rat) (p q : Poly) :
    evalAt2 c s nx ny nz c2 s2 (p ++ q) =
      evalAt2 c s nx ny nz c2 s2 p + evalAt2 c s nx ny nz c2 s2 q := by
  induction p with
  | nil => simp [evalAt2, Gauss.zero_add]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, evalAt2, ih]
      rw [← Gauss.add_assoc]

theorem evalAt2_single (c s nx ny nz c2 s2 : Rat) (a : Gauss) (m : Mono) :
    evalAt2 c s nx ny nz c2 s2 (single a m) = monoImage2 c s nx ny nz c2 s2 a m := by
  simp [evalAt2, single, monoImage2, Gauss.add_zero]

theorem evalAt2_mulMono (c s nx ny nz c2 s2 : Rat) (a : Gauss) (m : Mono) (q : Poly) :
    evalAt2 c s nx ny nz c2 s2 (mulMono a m q) =
      monoImage2 c s nx ny nz c2 s2 a m * evalAt2 c s nx ny nz c2 s2 q := by
  induction q with
  | nil => simp [mulMono, evalAt2, Gauss.mul_zero]
  | cons head rest ih =>
    cases head with
    | mk b n =>
      simp only [mulMono, evalAt2, ih, monoImage2, monoVal2_mul, Gauss.mul_add, Gauss.re_mul,
        Gauss.im_mul]
      ext <;> simp <;> grind

/-- `evalAt2` rispetta il prodotto. -/
theorem evalAt2_pmul (c s nx ny nz c2 s2 : Rat) (p q : Poly) :
    evalAt2 c s nx ny nz c2 s2 (pmul p q) =
      evalAt2 c s nx ny nz c2 s2 p * evalAt2 c s nx ny nz c2 s2 q := by
  induction p with
  | nil => simp [pmul, Universe.Quotient.mul, evalAt2, Gauss.zero_mul]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show pmul ((a, m) :: rest) q = mulMono a m q ++ pmul rest q from rfl, evalAt2_append,
        evalAt2_mulMono, ih]
      rw [show evalAt2 c s nx ny nz c2 s2 ((a, m) :: rest) =
        monoImage2 c s nx ny nz c2 s2 a m + evalAt2 c s nx ny nz c2 s2 rest from rfl,
        Gauss.add_mul]

theorem silent_single (a : Gauss) (m : Mono) (h : m.c2 = 0 ∧ m.s2 = 0) :
    ∀ x ∈ single a m, x.2.c2 = 0 ∧ x.2.s2 = 0 := by
  intro x hx
  simp only [single, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rw [hx]
  exact h

theorem silent_append {p q : Poly}
    (hp : ∀ x ∈ p, x.2.c2 = 0 ∧ x.2.s2 = 0)
    (hq : ∀ x ∈ q, x.2.c2 = 0 ∧ x.2.s2 = 0) :
    ∀ x ∈ p ++ q, x.2.c2 = 0 ∧ x.2.s2 = 0 := by
  intro x hx
  rw [List.mem_append] at hx
  cases hx with
  | inl hmem => exact hp x hmem
  | inr hmem => exact hq x hmem

/-- Senza esponenti `c2` e `s2`, le due valutazioni coincidono. -/
theorem evalAt2_agrees (c s nx ny nz c2 s2 : Rat) (p : Poly)
    (h : ∀ x ∈ p, x.2.c2 = 0 ∧ x.2.s2 = 0) :
    evalAt2 c s nx ny nz c2 s2 p = evalAt c s nx ny nz p := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      have hm := h (a, m) List.mem_cons_self
      have hrest : ∀ x ∈ rest, x.2.c2 = 0 ∧ x.2.s2 = 0 :=
        fun x hx => h x (List.mem_cons_of_mem _ hx)
      rw [evalAt2, evalAt, ih hrest, monoImage2, monoVal2_silent c s nx ny nz c2 s2 m hm]

/-- `gN` non contiene `c2` né `s2`: `evalAt2` lo legge come `evalAt`. -/
theorem evalAt2_gN (c s c2 s2 : Rat) :
    evalAt2 c s 1 0 0 c2 s2 gN = evalAt c s 1 0 0 gN := by
  apply evalAt2_agrees
  exact silent_append
    (silent_append
      (silent_append (silent_single _ _ ⟨rfl, rfl⟩) (silent_single _ _ ⟨rfl, rfl⟩))
      (silent_single _ _ ⟨rfl, rfl⟩))
    (silent_single _ _ ⟨rfl, rfl⟩)

/-! ### Sostituzione di `mx`, `my`, `mz` -/

/-- Valore di un monomio, con anche `mx`, `my`, `mz`. -/
def monoVal3 (c s nx ny nz c2 s2 mx my mz : Rat) (m : Mono) : Rat :=
  monoVal2 c s nx ny nz c2 s2 m * powR mx m.mx * powR my m.my * powR mz m.mz

/-- Immagine di un coefficiente sotto `c, s, n, c2, s2, m`. -/
def monoImage3 (c s nx ny nz c2 s2 mx my mz : Rat) (z : Gauss) (m : Mono) : Gauss :=
  ⟨z.re * monoVal3 c s nx ny nz c2 s2 mx my mz m,
    z.im * monoVal3 c s nx ny nz c2 s2 mx my mz m⟩

/-- Valuta un polinomio sostituendo anche `mx`, `my`, `mz`. `evalAt2` li ignora. -/
def evalAt3 (c s nx ny nz c2 s2 mx my mz : Rat) : Poly → Gauss
  | [] => 0
  | (a, m) :: rest =>
      monoImage3 c s nx ny nz c2 s2 mx my mz a m +
        evalAt3 c s nx ny nz c2 s2 mx my mz rest

theorem monoVal3_mul (c s nx ny nz c2 s2 mx my mz : Rat) (m n : Mono) :
    monoVal3 c s nx ny nz c2 s2 mx my mz (m.mul n) =
      monoVal3 c s nx ny nz c2 s2 mx my mz m *
        monoVal3 c s nx ny nz c2 s2 mx my mz n := by
  simp only [monoVal3]
  rw [monoVal2_mul]
  simp only [Mono.mul, powR_add]
  grind

theorem monoVal3_silent (c s nx ny nz c2 s2 mx my mz : Rat) (m : Mono)
    (h : m.mx = 0 ∧ m.my = 0 ∧ m.mz = 0) :
    monoVal3 c s nx ny nz c2 s2 mx my mz m = monoVal2 c s nx ny nz c2 s2 m := by
  simp [monoVal3, h.1, h.2.1, h.2.2, powR]

theorem monoImage3_mul (c s nx ny nz c2 s2 mx my mz : Rat) (a b : Gauss) (m n : Mono) :
    monoImage3 c s nx ny nz c2 s2 mx my mz (a * b) (m.mul n) =
      monoImage3 c s nx ny nz c2 s2 mx my mz a m *
        monoImage3 c s nx ny nz c2 s2 mx my mz b n := by
  simp only [monoImage3, monoVal3_mul, Gauss.re_mul, Gauss.im_mul]
  ext <;> simp <;> grind

theorem evalAt3_append (c s nx ny nz c2 s2 mx my mz : Rat) (p q : Poly) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (p ++ q) =
      evalAt3 c s nx ny nz c2 s2 mx my mz p +
        evalAt3 c s nx ny nz c2 s2 mx my mz q := by
  induction p with
  | nil => simp [evalAt3, Gauss.zero_add]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      simp only [List.cons_append, evalAt3, ih]
      rw [← Gauss.add_assoc]

theorem evalAt3_single (c s nx ny nz c2 s2 mx my mz : Rat) (a : Gauss) (m : Mono) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (single a m) =
      monoImage3 c s nx ny nz c2 s2 mx my mz a m := by
  simp [evalAt3, single, monoImage3, Gauss.add_zero]

theorem evalAt3_mulMono (c s nx ny nz c2 s2 mx my mz : Rat) (a : Gauss) (m : Mono)
    (q : Poly) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (mulMono a m q) =
      monoImage3 c s nx ny nz c2 s2 mx my mz a m *
        evalAt3 c s nx ny nz c2 s2 mx my mz q := by
  induction q with
  | nil => simp [mulMono, evalAt3, Gauss.mul_zero]
  | cons head rest ih =>
    cases head with
    | mk b n =>
      simp only [mulMono, evalAt3, ih, monoImage3, monoVal3_mul, Gauss.mul_add, Gauss.re_mul,
        Gauss.im_mul]
      ext <;> simp <;> grind

/-- `evalAt3` rispetta il prodotto. -/
theorem evalAt3_pmul (c s nx ny nz c2 s2 mx my mz : Rat) (p q : Poly) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (pmul p q) =
      evalAt3 c s nx ny nz c2 s2 mx my mz p *
        evalAt3 c s nx ny nz c2 s2 mx my mz q := by
  induction p with
  | nil => simp [pmul, Universe.Quotient.mul, evalAt3, Gauss.zero_mul]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show pmul ((a, m) :: rest) q = mulMono a m q ++ pmul rest q from rfl,
        evalAt3_append, evalAt3_mulMono, ih]
      rw [show evalAt3 c s nx ny nz c2 s2 mx my mz ((a, m) :: rest) =
        monoImage3 c s nx ny nz c2 s2 mx my mz a m +
          evalAt3 c s nx ny nz c2 s2 mx my mz rest from rfl, Gauss.add_mul]

theorem evalAt3_pneg (c s nx ny nz c2 s2 mx my mz : Rat) (p : Poly) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (pneg p) =
      -evalAt3 c s nx ny nz c2 s2 mx my mz p := by
  induction p with
  | nil =>
    simp [pneg, evalAt3]
    ext <;> simp
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show pneg ((a, m) :: rest) = (-a, m) :: pneg rest from rfl, evalAt3, ih]
      rw [show evalAt3 c s nx ny nz c2 s2 mx my mz ((a, m) :: rest) =
        monoImage3 c s nx ny nz c2 s2 mx my mz a m +
          evalAt3 c s nx ny nz c2 s2 mx my mz rest from rfl]
      ext <;> simp [monoImage3, Gauss.re_neg, Gauss.im_neg] <;> grind

theorem evalAt3_psub (c s nx ny nz c2 s2 mx my mz : Rat) (p q : Poly) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (psub p q) =
      evalAt3 c s nx ny nz c2 s2 mx my mz p +
        -evalAt3 c s nx ny nz c2 s2 mx my mz q := by
  rw [psub, evalAt3_append, evalAt3_pneg]

/-- `evalAt3` porta la scala di Gauss sul valore. -/
theorem evalAt3_scale (c s nx ny nz c2 s2 mx my mz : Rat) (z : Gauss) (p : Poly) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (scale z p) =
      z * evalAt3 c s nx ny nz c2 s2 mx my mz p := by
  induction p with
  | nil =>
    simp [scale, evalAt3]
    rw [Gauss.mul_zero]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show scale z ((a, m) :: rest) = (z * a, m) :: scale z rest from rfl]
      rw [show evalAt3 c s nx ny nz c2 s2 mx my mz ((z * a, m) :: scale z rest) =
        monoImage3 c s nx ny nz c2 s2 mx my mz (z * a) m +
          evalAt3 c s nx ny nz c2 s2 mx my mz (scale z rest) from rfl, ih]
      rw [show evalAt3 c s nx ny nz c2 s2 mx my mz ((a, m) :: rest) =
        monoImage3 c s nx ny nz c2 s2 mx my mz a m +
          evalAt3 c s nx ny nz c2 s2 mx my mz rest from rfl, Gauss.mul_add]
      have hterm :
          monoImage3 c s nx ny nz c2 s2 mx my mz (z * a) m =
            z * monoImage3 c s nx ny nz c2 s2 mx my mz a m := by
        ext <;> simp [monoImage3, Gauss.re_mul, Gauss.im_mul] <;> grind
      rw [hterm]

theorem conj_monoImage3 (c s nx ny nz c2 s2 mx my mz : Rat) (a : Gauss) (m : Mono) :
    Gauss.conj (monoImage3 c s nx ny nz c2 s2 mx my mz a m) =
      monoImage3 c s nx ny nz c2 s2 mx my mz (Gauss.conj a) m := by
  simp only [monoImage3, Gauss.conj]
  ext <;> simp <;> grind

theorem evalAt3_conj (c s nx ny nz c2 s2 mx my mz : Rat) (p : Poly) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (conjP p) =
      Gauss.conj (evalAt3 c s nx ny nz c2 s2 mx my mz p) := by
  induction p with
  | nil => simp [conjP, evalAt3, conj_zero]
  | cons head rest ih =>
    cases head with
    | mk a m =>
      rw [show conjP ((a, m) :: rest) = (Gauss.conj a, m) :: conjP rest from rfl]
      rw [show evalAt3 c s nx ny nz c2 s2 mx my mz ((Gauss.conj a, m) :: conjP rest) =
            monoImage3 c s nx ny nz c2 s2 mx my mz (Gauss.conj a) m +
              evalAt3 c s nx ny nz c2 s2 mx my mz (conjP rest) from rfl, ih,
        ← conj_monoImage3,
        show evalAt3 c s nx ny nz c2 s2 mx my mz ((a, m) :: rest) =
            monoImage3 c s nx ny nz c2 s2 mx my mz a m +
              evalAt3 c s nx ny nz c2 s2 mx my mz rest from rfl, conj_add]

/-- `|z|²` valutato con `evalAt3` è il modulo del valore. -/
theorem evalAt3_columnBorn (c s nx ny nz c2 s2 mx my mz : Rat) (p : Poly) :
    evalAt3 c s nx ny nz c2 s2 mx my mz (columnBorn p) =
      evalAt3 c s nx ny nz c2 s2 mx my mz p *
        Gauss.conj (evalAt3 c s nx ny nz c2 s2 mx my mz p) := by
  rw [columnBorn, evalAt3_pmul, evalAt3_conj]

theorem axisSilent_single (a : Gauss) (m : Mono) (h : m.mx = 0 ∧ m.my = 0 ∧ m.mz = 0) :
    ∀ x ∈ single a m, x.2.mx = 0 ∧ x.2.my = 0 ∧ x.2.mz = 0 := by
  intro x hx
  simp only [single, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rw [hx]
  exact h

theorem axisSilent_append {p q : Poly}
    (hp : ∀ x ∈ p, x.2.mx = 0 ∧ x.2.my = 0 ∧ x.2.mz = 0)
    (hq : ∀ x ∈ q, x.2.mx = 0 ∧ x.2.my = 0 ∧ x.2.mz = 0) :
    ∀ x ∈ p ++ q, x.2.mx = 0 ∧ x.2.my = 0 ∧ x.2.mz = 0 := by
  intro x hx
  rw [List.mem_append] at hx
  cases hx with
  | inl hmem => exact hp x hmem
  | inr hmem => exact hq x hmem

/-- Senza esponenti `mx`, `my`, `mz`, le due valutazioni coincidono. -/
theorem evalAt3_agrees (c s nx ny nz c2 s2 mx my mz : Rat) (p : Poly)
    (h : ∀ x ∈ p, x.2.mx = 0 ∧ x.2.my = 0 ∧ x.2.mz = 0) :
    evalAt3 c s nx ny nz c2 s2 mx my mz p = evalAt2 c s nx ny nz c2 s2 p := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | mk a m =>
      have hm := h (a, m) List.mem_cons_self
      have hrest : ∀ x ∈ rest, x.2.mx = 0 ∧ x.2.my = 0 ∧ x.2.mz = 0 :=
        fun x hx => h x (List.mem_cons_of_mem _ hx)
      rw [evalAt3, evalAt2, ih hrest, monoImage3, monoImage2,
        monoVal3_silent c s nx ny nz c2 s2 mx my mz m hm]

end Universe.Evaluation
