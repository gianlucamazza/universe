/-
Valutazione nel punto.

`evalAt` è un omomorfismo: rispetta `polySame`, il prodotto e il coniugio.
`eval_polySame` dice che due polinomi con gli stessi coefficienti hanno lo
stesso valore. `eval_pmul` e `eval_conj` portano prodotto e coniugio sui
valori di Gauss. `listEval` somma i coefficienti lungo un supporto senza
ripetizioni; `eval_cover` lo identifica con `evalAt`.
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

end Universe.Evaluation
