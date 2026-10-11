/-
n qubit, un albero binario perfetto.

`QState 0` è un'ampiezza. `node l r` divide sul primo qubit: `l` dove
legge `0`, `r` dove legge `1`. L'ordine delle celle è quello di `Quad`
e di `Oct` (`2i + k`, `4i + 2j + k`).

`normQ` somma `columnBorn` sulle foglie. `applyAt k` applica una
matrice `2×2` al qubit `k`. Sul qubit `0` mescola le due branche foglia
per foglia. Sul qubit `k + 1` agisce dentro entrambi i figli.

`norm_applyAt` mette `‖applyAt k U v‖² − ‖v‖²` in `(gC, gN)`, con
`U = evolution`. Sul qubit `0` è `literal_evolution_norm` su ogni
coppia di foglie corrispondenti, e il riordino è `polySame_append4_mid`.
Sul qubit `k + 1` la differenza è la somma delle due differenze dei
figli, via `inIdeal_append`. Il certificato Python lo controlla su
stati generici di `n ≤ 4` qubit, con `universe/qubits.py`.

`marginalAt k` è la coppia di Born del qubit `k`. `no_signalling_at`
dice che `applyAt b evolution` lascia quella coppia in `(gC, gN)`
quando `a ≠ b`. Se `b` sta nei figli, il bit alto si muove di
`norm_applyNat`. Se `b` è il bit alto, `mixRoot` accoppia foglie con
lo stesso valore di `a`, e la differenza è `zip_ideal`.

`applyAt_comm` dice che due matrici su qubit diversi commutano, foglia
per foglia, a coefficienti. `reduceAt` è la traccia parziale su un
qubit: la diagonale è `marginalAt`. Su `|ψ⟩` al qubit `k` e un resto
sugli altri, è `‖resto‖² |ψ⟩⟨ψ|`.

`cnotFrom0 k` è il `CNOT` dal qubit `0` al qubit `k`. `k = 0` lascia
lo stato: il controllo non è un bersaglio. `fanout` li applica tutti
su `|ψ⟩ ⊗ |0…0⟩`. `fanout_ghz` è `α|0…0⟩ + β|1…1⟩`: ogni altra foglia
è il polinomio zero. `fanout_agree` somma il peso di Born sulle celle
in cui due qubit differiscono, ed è zero. `fanout_decoherence`, per
`n ≥ 2`, rende il sistema diagonale con `bornPair ψ`.
-/
import Universe.Composition
import Universe.Epistemology
import Universe.Observer

namespace Universe.Qubits

open Universe.Composition
open Universe.Dynamics
open Universe.Epistemology
open Universe.Observer
open Universe.Qubit
open Universe.Quotient hiding mul

/-- Albero perfetto di `n` qubit. `n` è esplicito: `autoImplicit` è spento. -/
inductive QState : Nat → Type where
  | leaf : Poly → QState 0
  | node : {n : Nat} → QState n → QState n → QState (n + 1)

/-- Somma dei moduli quadri sulle foglie. -/
def normQ : {n : Nat} → QState n → Poly
  | _, .leaf z => columnBorn z
  | _, .node l r => normQ l ++ normQ r

/-- Le due branche dopo una matrice sul qubit alto. `lo` è la riga `0`. -/
structure Mix (n : Nat) where
  lo : QState n
  hi : QState n

/-- Mescola due alberi della stessa profondità, foglia per foglia. -/
def mixRoot (U : Mat) : {n : Nat} → QState n → QState n → Mix n
  | _, .leaf α, .leaf β =>
    { lo := .leaf (pmul U.a00 α ++ pmul U.a01 β)
    , hi := .leaf (pmul U.a10 α ++ pmul U.a11 β) }
  | _, .node a b, .node c d =>
    { lo := .node (mixRoot U a c).lo (mixRoot U b d).lo
    , hi := .node (mixRoot U a c).hi (mixRoot U b d).hi }

/-- `|Uγ|²` su ogni coppia di foglie corrispondenti. -/
def zipNorm (U : Mat) : {n : Nat} → QState n → QState n → Poly
  | _, .leaf α, .leaf β => literalNorm U α β
  | _, .node a b, .node c d => zipNorm U a c ++ zipNorm U b d

/-- `|α|² + |β|²` sulle stesse coppie. -/
def zipBorn : {n : Nat} → QState n → QState n → Poly
  | _, .leaf α, .leaf β => columnBorn α ++ columnBorn β
  | _, .node a b, .node c d => zipBorn a c ++ zipBorn b d

/-- La norma delle due branche mescolate ha i coefficienti di `zipNorm`. -/
theorem norm_mix (U : Mat) : {n : Nat} → (l r : QState n) →
    polySame (normQ (mixRoot U l r).lo ++ normQ (mixRoot U l r).hi) (zipNorm U l r)
  | _, .leaf _, .leaf _ => polySame_refl _
  | _, .node a b, .node c d =>
    polySame.trans
      (polySame_append4_mid
        (normQ (mixRoot U a c).lo) (normQ (mixRoot U b d).lo)
        (normQ (mixRoot U a c).hi) (normQ (mixRoot U b d).hi))
      (polySame_append (norm_mix U a c) (norm_mix U b d))

/-- `‖l‖² + ‖r‖²` ha i coefficienti di `zipBorn`. Il passo è il crocevia. -/
theorem norm_zipBorn : {n : Nat} → (l r : QState n) →
    polySame (normQ l ++ normQ r) (zipBorn l r)
  | _, .leaf _, .leaf _ => polySame_refl _
  | _, .node a b, .node c d =>
    polySame.trans
      (polySame_append4_mid (normQ a) (normQ b) (normQ c) (normQ d))
      (polySame_append (norm_zipBorn a c) (norm_zipBorn b d))

/-- La somma delle differenze di coppia sta in `(gC, gN)`. -/
theorem zip_ideal : {n : Nat} → (l r : QState n) →
    inIdeal (psub (zipNorm evolution l r) (zipBorn l r))
  | _, .leaf α, .leaf β => literal_evolution_norm α β
  | _, .node a b, .node c d =>
    inIdeal_polySame
      (polySame_psub_append (zipNorm evolution a c) (zipNorm evolution b d)
        (zipBorn a c) (zipBorn b d))
      (inIdeal_append (zip_ideal a c) (zip_ideal b d))

/-- Ricorsione sull'indice. `k = 0` è il qubit alto; `k + 1` scende. -/
def applyNat (k : Nat) (U : Mat) : {n : Nat} → QState n → QState n
  | 0, v => v
  | _ + 1, .node l r =>
    match k with
    | 0 => .node (mixRoot U l r).lo (mixRoot U l r).hi
    | j + 1 => .node (applyNat j U l) (applyNat j U r)

theorem norm_root {n : Nat} (l r : QState n) :
    inIdeal (psub (normQ (applyNat 0 evolution (.node l r))) (normQ (.node l r))) :=
  inIdeal_polySame (polySame_psub (norm_mix evolution l r) (norm_zipBorn l r))
    (zip_ideal l r)

theorem norm_child {n : Nat} (k : Nat) (l r : QState n)
    (hl : inIdeal (psub (normQ (applyNat k evolution l)) (normQ l)))
    (hr : inIdeal (psub (normQ (applyNat k evolution r)) (normQ r))) :
    inIdeal
      (psub (normQ (applyNat (k + 1) evolution (.node l r))) (normQ (.node l r))) :=
  inIdeal_polySame
    (polySame_psub_append (normQ (applyNat k evolution l)) (normQ (applyNat k evolution r))
      (normQ l) (normQ r))
    (inIdeal_append hl hr)

theorem norm_applyNat (k : Nat) : {n : Nat} → (v : QState n) →
    inIdeal (psub (normQ (applyNat k evolution v)) (normQ v))
  | 0, _ => by
    simp only [applyNat]
    exact inIdeal_of_polySame (polySame_refl _)
  | _ + 1, .node l r =>
    match k with
    | 0 => norm_root l r
    | j + 1 => norm_child j l r (norm_applyNat j l) (norm_applyNat j r)

/-- Matrice `2×2` sul qubit `k`. `k = 0` è il bit alto. -/
def applyAt {n : Nat} (k : Fin n) (U : Mat) (v : QState n) : QState n :=
  applyNat k.val U v

/-- `‖applyAt k U v‖² − ‖v‖²` sta in `(gC, gN)`. -/
theorem norm_applyAt {n : Nat} (k : Fin n) (v : QState n) :
    inIdeal (psub (normQ (applyAt k evolution v)) (normQ v)) :=
  norm_applyNat k.val v

/-! ### Il marginale di un qubit -/

/-- Coppia di Born del qubit `k`. `k = 0` è il bit alto.

Su una foglia non c'è un qubit: la coppia è zero. Su `node l r`,
`k = 0` legge `‖l‖²` e `‖r‖²`. `k + 1` somma le coppie dei due figli. -/
def marginalNat (k : Nat) : {n : Nat} → QState n → Pair
  | _, .leaf _ => ⟨[], []⟩
  | _, .node l r =>
    match k with
    | 0 => ⟨normQ l, normQ r⟩
    | j + 1 =>
      ⟨(marginalNat j l).a0 ++ (marginalNat j r).a0,
        (marginalNat j l).a1 ++ (marginalNat j r).a1⟩

/-- Coppia di Born del qubit `k`. -/
def marginalAt {n : Nat} (k : Fin n) (v : QState n) : Pair :=
  marginalNat k.val v

/-- `zipNorm` sulle fibre del qubit `k` di due alberi appaiati.

`k = 0` accoppia i figli sinistri fra loro e i destri fra loro. -/
def zipMarginal (k : Nat) (U : Mat) : {n : Nat} → QState n → QState n → Pair
  | _, .leaf _, .leaf _ => ⟨[], []⟩
  | _, .node a b, .node c d =>
    match k with
    | 0 => ⟨zipNorm U a c, zipNorm U b d⟩
    | j + 1 =>
      ⟨(zipMarginal j U a c).a0 ++ (zipMarginal j U b d).a0,
        (zipMarginal j U a c).a1 ++ (zipMarginal j U b d).a1⟩

/-- Le stesse fibre, lette con `zipBorn`. -/
def bornMarginal (k : Nat) : {n : Nat} → QState n → QState n → Pair
  | _, .leaf _, .leaf _ => ⟨[], []⟩
  | _, .node a b, .node c d =>
    match k with
    | 0 => ⟨zipBorn a c, zipBorn b d⟩
    | j + 1 =>
      ⟨(bornMarginal j a c).a0 ++ (bornMarginal j b d).a0,
        (bornMarginal j a c).a1 ++ (bornMarginal j b d).a1⟩

/-- Il marginale dei due alberi ha i coefficienti di `bornMarginal`.

Il passo `k + 1` è il crocevia `polySame_append4_mid`. -/
theorem marginal_bornMarginal (k : Nat) : {n : Nat} → (l r : QState n) →
    polySame ((marginalNat k l).a0 ++ (marginalNat k r).a0) (bornMarginal k l r).a0 ∧
      polySame ((marginalNat k l).a1 ++ (marginalNat k r).a1) (bornMarginal k l r).a1
  | _, .leaf _, .leaf _ => by
    simp only [marginalNat, bornMarginal, List.append_nil]
    exact ⟨polySame_refl _, polySame_refl _⟩
  | _, .node a b, .node c d =>
    match k with
    | 0 => ⟨norm_zipBorn a c, norm_zipBorn b d⟩
    | j + 1 =>
      ⟨polySame.trans
          (polySame_append4_mid (marginalNat j a).a0 (marginalNat j b).a0
            (marginalNat j c).a0 (marginalNat j d).a0)
          (polySame_append (marginal_bornMarginal j a c).1 (marginal_bornMarginal j b d).1),
        polySame.trans
          (polySame_append4_mid (marginalNat j a).a1 (marginalNat j b).a1
            (marginalNat j c).a1 (marginalNat j d).a1)
          (polySame_append (marginal_bornMarginal j a c).2 (marginal_bornMarginal j b d).2)⟩

/-- Dopo `mixRoot`, il marginale del qubit `k` ha i coefficienti di `zipMarginal`. -/
theorem zipMarginal_mix (k : Nat) (U : Mat) : {n : Nat} → (l r : QState n) →
    polySame
        ((marginalNat k (mixRoot U l r).lo).a0 ++ (marginalNat k (mixRoot U l r).hi).a0)
        (zipMarginal k U l r).a0 ∧
      polySame
        ((marginalNat k (mixRoot U l r).lo).a1 ++ (marginalNat k (mixRoot U l r).hi).a1)
        (zipMarginal k U l r).a1
  | _, .leaf _, .leaf _ => by
    simp only [marginalNat, mixRoot, zipMarginal, List.append_nil]
    exact ⟨polySame_refl _, polySame_refl _⟩
  | _, .node a b, .node c d =>
    match k with
    | 0 => ⟨norm_mix U a c, norm_mix U b d⟩
    | j + 1 =>
      ⟨polySame.trans
          (polySame_append4_mid
            (marginalNat j (mixRoot U a c).lo).a0 (marginalNat j (mixRoot U b d).lo).a0
            (marginalNat j (mixRoot U a c).hi).a0 (marginalNat j (mixRoot U b d).hi).a0)
          (polySame_append (zipMarginal_mix j U a c).1 (zipMarginal_mix j U b d).1),
        polySame.trans
          (polySame_append4_mid
            (marginalNat j (mixRoot U a c).lo).a1 (marginalNat j (mixRoot U b d).lo).a1
            (marginalNat j (mixRoot U a c).hi).a1 (marginalNat j (mixRoot U b d).hi).a1)
          (polySame_append (zipMarginal_mix j U a c).2 (zipMarginal_mix j U b d).2)⟩

/-- La differenza delle due letture sta in `(gC, gN)`.

Sul bit alto è `zip_ideal`. Sul qubit `k + 1` è `inIdeal_append`. -/
theorem zipMarginal_ideal (k : Nat) : {n : Nat} → (l r : QState n) →
    inIdeal (psub (zipMarginal k evolution l r).a0 (bornMarginal k l r).a0) ∧
      inIdeal (psub (zipMarginal k evolution l r).a1 (bornMarginal k l r).a1)
  | _, .leaf _, .leaf _ => by
    simp only [zipMarginal, bornMarginal]
    exact ⟨inIdeal_of_polySame (polySame_refl _), inIdeal_of_polySame (polySame_refl _)⟩
  | _, .node a b, .node c d =>
    match k with
    | 0 => ⟨zip_ideal a c, zip_ideal b d⟩
    | j + 1 =>
      ⟨inIdeal_polySame
          (polySame_psub_append (zipMarginal j evolution a c).a0 (zipMarginal j evolution b d).a0
            (bornMarginal j a c).a0 (bornMarginal j b d).a0)
          (inIdeal_append (zipMarginal_ideal j a c).1 (zipMarginal_ideal j b d).1),
        inIdeal_polySame
          (polySame_psub_append (zipMarginal j evolution a c).a1 (zipMarginal j evolution b d).a1
            (bornMarginal j a c).a1 (bornMarginal j b d).a1)
          (inIdeal_append (zipMarginal_ideal j a c).2 (zipMarginal_ideal j b d).2)⟩

/-- `U` sul bit alto non cambia il marginale di un qubit più basso.

Le foglie accoppiate da `mixRoot` hanno lo stesso valore su quel qubit. -/
theorem no_signalling_root {n : Nat} (k : Nat) (l r : QState n) :
    inIdeal
        (psub (marginalNat (k + 1) (applyNat 0 evolution (.node l r))).a0
          (marginalNat (k + 1) (.node l r)).a0) ∧
      inIdeal
        (psub (marginalNat (k + 1) (applyNat 0 evolution (.node l r))).a1
          (marginalNat (k + 1) (.node l r)).a1) := by
  have hU := zipMarginal_mix k evolution l r
  have hB := marginal_bornMarginal k l r
  have hI := zipMarginal_ideal k l r
  exact
    ⟨inIdeal_polySame (polySame_psub hU.1 hB.1) hI.1,
      inIdeal_polySame (polySame_psub hU.2 hB.2) hI.2⟩

/-- `U` dentro i figli non cambia il marginale del bit alto.

Ogni componente è `‖applyNat j U ·‖² − ‖·‖²`, cioè `norm_applyNat`. -/
theorem no_signalling_high {n : Nat} (j : Nat) (l r : QState n) :
    inIdeal
        (psub (marginalNat 0 (applyNat (j + 1) evolution (.node l r))).a0
          (marginalNat 0 (.node l r)).a0) ∧
      inIdeal
        (psub (marginalNat 0 (applyNat (j + 1) evolution (.node l r))).a1
          (marginalNat 0 (.node l r)).a1) :=
  ⟨norm_applyNat j l, norm_applyNat j r⟩

/-- `U` dentro i figli non cambia un marginale anch'esso dentro i figli.

La differenza è la somma delle due differenze, via `polySame_psub_append`. -/
theorem no_signalling_child {n : Nat} (i j : Nat) (l r : QState n)
    (hl :
      inIdeal (psub (marginalNat i (applyNat j evolution l)).a0 (marginalNat i l).a0) ∧
        inIdeal (psub (marginalNat i (applyNat j evolution l)).a1 (marginalNat i l).a1))
    (hr :
      inIdeal (psub (marginalNat i (applyNat j evolution r)).a0 (marginalNat i r).a0) ∧
        inIdeal (psub (marginalNat i (applyNat j evolution r)).a1 (marginalNat i r).a1)) :
    inIdeal
        (psub (marginalNat (i + 1) (applyNat (j + 1) evolution (.node l r))).a0
          (marginalNat (i + 1) (.node l r)).a0) ∧
      inIdeal
        (psub (marginalNat (i + 1) (applyNat (j + 1) evolution (.node l r))).a1
          (marginalNat (i + 1) (.node l r)).a1) :=
  ⟨inIdeal_polySame (polySame_psub_append _ _ _ _) (inIdeal_append hl.1 hr.1),
    inIdeal_polySame (polySame_psub_append _ _ _ _) (inIdeal_append hl.2 hr.2)⟩

/-- `applyNat b evolution` lascia il marginale del qubit `a ≠ b` in `(gC, gN)`. -/
theorem no_signalling_nat (a b : Nat) (h : a ≠ b) :
    {n : Nat} → a < n → b < n → (v : QState n) →
      inIdeal (psub (marginalNat a (applyNat b evolution v)).a0 (marginalNat a v).a0) ∧
        inIdeal (psub (marginalNat a (applyNat b evolution v)).a1 (marginalNat a v).a1)
  | 0, ha, _, _ => absurd ha (Nat.not_lt_zero _)
  | _ + 1, ha, hb, .node l r =>
    match b, a with
    | 0, 0 => absurd rfl h
    | 0, _ + 1 => no_signalling_root _ l r
    | _ + 1, 0 => no_signalling_high _ l r
    | j + 1, i + 1 =>
      no_signalling_child i j l r
        (no_signalling_nat i j (fun eq => h (congrArg Nat.succ eq))
          (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb) l)
        (no_signalling_nat i j (fun eq => h (congrArg Nat.succ eq))
          (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb) r)

/-- Un unitario sul qubit `b` non cambia la coppia di Born del qubit `a ≠ b`.

Entrambe le componenti stanno in `(gC, gN)`. -/
theorem no_signalling_at {n : Nat} (a b : Fin n) (h : a ≠ b) (v : QState n) :
    inIdeal (psub (marginalAt a (applyAt b evolution v)).a0 (marginalAt a v).a0) ∧
      inIdeal (psub (marginalAt a (applyAt b evolution v)).a1 (marginalAt a v).a1) :=
  no_signalling_nat a.val b.val (Fin.val_ne_of_ne h) a.isLt b.isLt v

/-! ### Porte su qubit diversi -/

/-- Due alberi hanno le stesse foglie, a coefficienti. -/
def qstateSame : {n : Nat} → QState n → QState n → Prop
  | _, .leaf z, .leaf w => polySame z w
  | _, .node l r, .node l' r' => qstateSame l l' ∧ qstateSame r r'

theorem qstateSame_symm : {n : Nat} → (v w : QState n) → qstateSame v w → qstateSame w v
  | _, .leaf _, .leaf _, h => polySame.symm h
  | _, .node _ _, .node _ _, h => ⟨qstateSame_symm _ _ h.1, qstateSame_symm _ _ h.2⟩

/-- `(p · c) + (q · c)` ha i coefficienti di `(p + q) · c`. -/
theorem polySame_sum_right (p q c : Poly) :
    polySame (pmul p c ++ pmul q c) (pmul (p ++ q) c) :=
  polySame.symm fun t => by rw [pmul_append_left]

/-- Le due associazioni di due matrici su due qubit hanno gli stessi coefficienti.

`u` agisce sul bit alto, `v` sul bit basso. I quattro `x` sono le foglie. -/
theorem polySame_commute_entries (u0 u1 v0 v1 x00 x01 x10 x11 : Poly) :
    polySame
      (pmul u0 (pmul v0 x00 ++ pmul v1 x01) ++ pmul u1 (pmul v0 x10 ++ pmul v1 x11))
      (pmul v0 (pmul u0 x00 ++ pmul u1 x10) ++ pmul v1 (pmul u0 x01 ++ pmul u1 x11)) := by
  have hL :=
    polySame_append (polySame_mul_append_right u0 (pmul v0 x00) (pmul v1 x01))
      (polySame_mul_append_right u1 (pmul v0 x10) (pmul v1 x11))
  have hR :=
    polySame_append (polySame_mul_append_right v0 (pmul u0 x00) (pmul u1 x10))
      (polySame_mul_append_right v1 (pmul u0 x01) (pmul u1 x11))
  exact polySame.trans hL
    (polySame.trans
      (polySame_append
        (polySame_append (slide_right u0 v0 x00) (slide_right u0 v1 x01))
        (polySame_append (slide_right u1 v0 x10) (slide_right u1 v1 x11)))
      (polySame.trans
        (polySame_append4_mid (pmul v0 (pmul u0 x00)) (pmul v1 (pmul u0 x01))
          (pmul v0 (pmul u1 x10)) (pmul v1 (pmul u1 x11)))
        hR.symm))

/-- `mixRoot` di due matrici commuta sulle quattro uscite, foglia per foglia.

Il passo è lo stesso crocevia su ciascuno dei due figli. -/
theorem mix_mix (U V : Mat) : {n : Nat} → (a b c d : QState n) →
    qstateSame (mixRoot U (mixRoot V a b).lo (mixRoot V c d).lo).lo
        (mixRoot V (mixRoot U a c).lo (mixRoot U b d).lo).lo ∧
      qstateSame (mixRoot U (mixRoot V a b).hi (mixRoot V c d).hi).lo
          (mixRoot V (mixRoot U a c).lo (mixRoot U b d).lo).hi ∧
        qstateSame (mixRoot U (mixRoot V a b).lo (mixRoot V c d).lo).hi
            (mixRoot V (mixRoot U a c).hi (mixRoot U b d).hi).lo ∧
          qstateSame (mixRoot U (mixRoot V a b).hi (mixRoot V c d).hi).hi
            (mixRoot V (mixRoot U a c).hi (mixRoot U b d).hi).hi
  | _, .leaf α, .leaf β, .leaf γ, .leaf δ => by
    simp only [mixRoot, qstateSame]
    exact ⟨polySame_commute_entries U.a00 U.a01 V.a00 V.a01 α β γ δ,
      polySame_commute_entries U.a00 U.a01 V.a10 V.a11 α β γ δ,
      polySame_commute_entries U.a10 U.a11 V.a00 V.a01 α β γ δ,
      polySame_commute_entries U.a10 U.a11 V.a10 V.a11 α β γ δ⟩
  | _, .node a0 a1, .node b0 b1, .node c0 c1, .node d0 d1 => by
    have h0 := mix_mix U V a0 b0 c0 d0
    have h1 := mix_mix U V a1 b1 c1 d1
    simp only [mixRoot, qstateSame]
    exact ⟨⟨h0.1, h1.1⟩, ⟨h0.2.1, h1.2.1⟩, ⟨h0.2.2.1, h1.2.2.1⟩, ⟨h0.2.2.2, h1.2.2.2⟩⟩

/-- Una matrice sul bit alto commuta con una matrice dentro i due alberi. -/
theorem mix_applyNat (j : Nat) (U V : Mat) : {n : Nat} → (l r : QState n) →
    qstateSame (mixRoot U (applyNat j V l) (applyNat j V r)).lo
        (applyNat j V (mixRoot U l r).lo) ∧
      qstateSame (mixRoot U (applyNat j V l) (applyNat j V r)).hi
        (applyNat j V (mixRoot U l r).hi)
  | _, .leaf _, .leaf _ => by
    simp only [applyNat, mixRoot, qstateSame]
    exact ⟨polySame_refl _, polySame_refl _⟩
  | _, .node a b, .node c d =>
    match j with
    | 0 => by
      have h := mix_mix U V a b c d
      simp only [applyNat, mixRoot, qstateSame]
      exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩
    | i + 1 => by
      have hac := mix_applyNat i U V a c
      have hbd := mix_applyNat i U V b d
      simp only [applyNat, mixRoot, qstateSame]
      exact ⟨⟨hac.1, hbd.1⟩, ⟨hac.2, hbd.2⟩⟩

/-- `applyNat a` e `applyNat b` commutano quando `a ≠ b`. -/
theorem applyNat_comm (a b : Nat) (h : a ≠ b) (U V : Mat) :
    {n : Nat} → a < n → b < n → (v : QState n) →
      qstateSame (applyNat a U (applyNat b V v)) (applyNat b V (applyNat a U v))
  | 0, ha, _, _ => absurd ha (Nat.not_lt_zero _)
  | _ + 1, ha, hb, .node l r =>
    match a, b with
    | 0, 0 => absurd rfl h
    | 0, j + 1 => by
      simp only [applyNat, qstateSame]
      exact mix_applyNat j U V l r
    | i + 1, 0 => by
      simp only [applyNat, qstateSame]
      exact ⟨qstateSame_symm _ _ (mix_applyNat i V U l r).1,
        qstateSame_symm _ _ (mix_applyNat i V U l r).2⟩
    | i + 1, j + 1 => by
      simp only [applyNat, qstateSame]
      exact ⟨applyNat_comm i j (fun eq => h (congrArg Nat.succ eq)) U V
          (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb) l,
        applyNat_comm i j (fun eq => h (congrArg Nat.succ eq)) U V
          (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb) r⟩

/-- Due matrici su qubit diversi commutano, foglia per foglia.

L'uguaglianza è `polySame` su ogni foglia: il prodotto dei polinomi
non è commutativo come lista. -/
theorem applyAt_comm {n : Nat} (a b : Fin n) (h : a ≠ b) (U V : Mat) (v : QState n) :
    qstateSame (applyAt a U (applyAt b V v)) (applyAt b V (applyAt a U v)) :=
  applyNat_comm a.val b.val (Fin.val_ne_of_ne h) U V a.isLt b.isLt v

/-! ### Lo stato di un qubit -/

/-- Prodotto di ogni foglia per lo stesso polinomio. -/
def scaleQ (μ : Poly) : {n : Nat} → QState n → QState n
  | _, .leaf z => .leaf (pmul μ z)
  | _, .node l r => .node (scaleQ μ l) (scaleQ μ r)

/-- Somma `α · conj(β)` sulle foglie corrispondenti di due alberi. -/
def zipCoh : {n : Nat} → QState n → QState n → Poly
  | _, .leaf α, .leaf β => pmul α (conjP β)
  | _, .node a b, .node c d => zipCoh a c ++ zipCoh b d

/-- `‖scale μ v‖²` ha i coefficienti di `‖v‖² · |μ|²`. -/
theorem norm_scale (μ : Poly) : {n : Nat} → (v : QState n) →
    polySame (normQ (scaleQ μ v)) (pmul (normQ v) (columnBorn μ))
  | _, .leaf z => columnBorn_pmul μ z
  | _, .node l r =>
    polySame.trans (polySame_append (norm_scale μ l) (norm_scale μ r))
      (polySame_sum_right (normQ l) (normQ r) (columnBorn μ))

/-- La coerenza di due copie scalate è `‖v‖² · p conj(y)`. -/
theorem coh_scale (p y : Poly) : {n : Nat} → (v : QState n) →
    polySame (zipCoh (scaleQ p v) (scaleQ y v)) (pmul (normQ v) (pmul p (conjP y)))
  | _, .leaf z => coherence_scale p y z
  | _, .node l r =>
    polySame.trans (polySame_append (coh_scale p y l) (coh_scale p y r))
      (polySame_sum_right (normQ l) (normQ r) (pmul p (conjP y)))

/-- Traccia parziale sul qubit `k`. `k = 0` è il bit alto.

Su una foglia non c'è un qubit: la matrice è zero. Su `node l r`,
`k = 0` accoppia le due branche con `zipCoh`. `k + 1` somma le matrici
dei due figli, perché il bit alto si traccia. -/
def reduceNat (k : Nat) : {n : Nat} → QState n → Mat
  | _, .leaf _ => matZero
  | _, .node l r =>
    match k with
    | 0 => ⟨normQ l, zipCoh l r, zipCoh r l, normQ r⟩
    | j + 1 => matAdd (reduceNat j l) (reduceNat j r)

/-- Traccia parziale sul qubit `k`. -/
def reduceAt {n : Nat} (k : Fin n) (v : QState n) : Mat :=
  reduceNat k.val v

/-- La diagonale della traccia parziale è la coppia di Born. -/
theorem reduceNat_diag (k : Nat) : {n : Nat} → (v : QState n) →
    (reduceNat k v).a00 = (marginalNat k v).a0 ∧
      (reduceNat k v).a11 = (marginalNat k v).a1
  | _, .leaf _ => by
    unfold reduceNat marginalNat matZero
    constructor <;> rfl
  | _, .node l r =>
    match k with
    | 0 => ⟨rfl, rfl⟩
    | j + 1 => by
      have hl := reduceNat_diag j l
      have hr := reduceNat_diag j r
      simp only [reduceNat, marginalNat, matAdd]
      exact ⟨by rw [hl.1, hr.1], by rw [hl.2, hr.2]⟩

/-- La diagonale di `reduceAt k` è `marginalAt k`. -/
theorem reduceAt_diag {n : Nat} (k : Fin n) (v : QState n) :
    ⟨(reduceAt k v).a00, (reduceAt k v).a11⟩ = marginalAt k v := by
  have h := reduceNat_diag k.val v
  simp only [reduceAt, marginalAt]
  exact Pair.ext h.1 h.2

/-- `|ψ⟩` sul qubit `k`, `rest` sugli altri, nell'ordine dei bit.

`k = 0` scala le due copie di `rest`. `k + 1` lascia il bit alto al
resto e scende nei due figli. -/
def embedAt (ψ : Pair) : {n : Nat} → Fin (n + 1) → QState n → QState (n + 1)
  | _, ⟨0, _⟩, v => .node (scaleQ ψ.a0 v) (scaleQ ψ.a1 v)
  | 0, ⟨j + 1, h⟩, _ => False.elim (Nat.not_lt_zero j (Nat.lt_of_succ_lt_succ h))
  | _ + 1, ⟨j + 1, h⟩, .node l r =>
    .node (embedAt ψ ⟨j, Nat.lt_of_succ_lt_succ h⟩ l)
      (embedAt ψ ⟨j, Nat.lt_of_succ_lt_succ h⟩ r)

/-- Su un prodotto, la traccia parziale è `‖resto‖² |ψ⟩⟨ψ|`. -/
theorem reduceAt_product (ψ : Pair) : {n : Nat} → (k : Fin (n + 1)) → (rest : QState n) →
    matSame (reduceAt k (embedAt ψ k rest)) (matScale (normQ rest) (outer ψ))
  | _, ⟨0, _⟩, rest => by
    simp only [embedAt, reduceAt, reduceNat, matScale, outer]
    exact ⟨norm_scale ψ.a0 rest, coh_scale ψ.a0 ψ.a1 rest, coh_scale ψ.a1 ψ.a0 rest,
      norm_scale ψ.a1 rest⟩
  | 0, ⟨j + 1, h⟩, _ => False.elim (Nat.not_lt_zero j (Nat.lt_of_succ_lt_succ h))
  | _ + 1, ⟨j + 1, h⟩, .node l r => by
    simp only [embedAt, reduceAt, reduceNat, matAdd, matScale, normQ]
    have hl := reduceAt_product ψ ⟨j, Nat.lt_of_succ_lt_succ h⟩ l
    have hr := reduceAt_product ψ ⟨j, Nat.lt_of_succ_lt_succ h⟩ r
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact polySame.trans (polySame_append hl.1 hr.1)
        (polySame_sum_right (normQ l) (normQ r) (outer ψ).a00)
    · exact polySame.trans (polySame_append hl.2.1 hr.2.1)
        (polySame_sum_right (normQ l) (normQ r) (outer ψ).a01)
    · exact polySame.trans (polySame_append hl.2.2.1 hr.2.2.1)
        (polySame_sum_right (normQ l) (normQ r) (outer ψ).a10)
    · exact polySame.trans (polySame_append hl.2.2.2 hr.2.2.2)
        (polySame_sum_right (normQ l) (normQ r) (outer ψ).a11)

/-! ### n osservatori -/

/-- Ogni foglia è il polinomio zero. -/
def zeroQ : {n : Nat} → QState n
  | 0 => .leaf []
  | _ + 1 => .node zeroQ zeroQ

/-- `|0…0⟩`. La foglia tutta zero vale `1`. -/
def ket0Q : {n : Nat} → QState n
  | 0 => .leaf (single 1 Mono.one)
  | _ + 1 => .node ket0Q zeroQ

/-- `|1…1⟩`. La foglia tutta uno vale `1`. -/
def ket1Q : {n : Nat} → QState n
  | 0 => .leaf (single 1 Mono.one)
  | _ + 1 => .node zeroQ ket1Q

/-- Ampiezza `z` su `|0…0⟩`, zero sulle altre foglie. -/
def onZero (z : Poly) : {n : Nat} → QState n
  | 0 => .leaf z
  | _ + 1 => .node (onZero z) zeroQ

/-- Ampiezza `z` su `|1…1⟩`, zero sulle altre foglie. -/
def onOne (z : Poly) : {n : Nat} → QState n
  | 0 => .leaf z
  | _ + 1 => .node zeroQ (onOne z)

/-- `α|0…0⟩ + β|1…1⟩`. Le altre foglie sono il polinomio zero. -/
def ghz (ψ : Pair) : {n : Nat} → QState n
  | 0 => .leaf []
  | _ + 1 => .node (onZero ψ.a0) (onOne ψ.a1)

/-- Capovolge il qubit `k`. `k = 0` scambia i due figli. -/
def flipNat (k : Nat) : {n : Nat} → QState n → QState n
  | 0, v => v
  | _ + 1, .node l r =>
    match k with
    | 0 => .node r l
    | j + 1 => .node (flipNat j l) (flipNat j r)

/-- Capovolge i qubit da `k` in poi. `flipFrom 0` li capovolge tutti. -/
def flipFrom (k : Nat) : {n : Nat} → QState n → QState n
  | 0, v => v
  | _ + 1, .node l r =>
    match k with
    | 0 => .node (flipFrom 0 r) (flipFrom 0 l)
    | j + 1 => .node (flipFrom j l) (flipFrom j r)

/-- `CNOT` dal qubit `0` al qubit `k`.

Il controllo è il bit alto. Il ramo `0` resta. Nel ramo `1` si
capovolge il qubit `k`. `k = 0` è l'identità. -/
def cnotFrom0Nat (k : Nat) : {n : Nat} → QState n → QState n
  | 0, v => v
  | _ + 1, .node l r =>
    match k with
    | 0 => .node l r
    | j + 1 => .node l (flipNat j r)

/-- `CNOT` dal qubit `0` al qubit `k`. -/
def cnotFrom0 {n : Nat} (k : Fin n) (v : QState n) : QState n :=
  cnotFrom0Nat k.val v

/-- `cnotFrom0` verso i qubit `k, k + 1, …`. `k = 0` parte dal primo bersaglio. -/
def cnotsFrom (k : Nat) : {n : Nat} → QState n → QState n
  | 0, v => v
  | _ + 1, .node l r =>
    match k with
    | 0 => .node l (flipFrom 0 r)
    | j + 1 => .node l (flipFrom j r)

/-- Tutti i `CNOT` dal qubit `0` verso gli altri qubit. -/
def fanoutNat : {n : Nat} → QState n → QState n :=
  cnotsFrom 0

/-- `flipNat k` dopo i capovolgimenti da `k + 1` in poi è `flipFrom k`. -/
theorem flipNat_flipFrom (k : Nat) : {n : Nat} → (v : QState n) →
    flipNat k (flipFrom (k + 1) v) = flipFrom k v
  | 0, _ => by simp only [flipNat, flipFrom]
  | _ + 1, .node l r =>
    match k with
    | 0 => by simp only [flipNat, flipFrom]
    | j + 1 => by
      simp only [flipNat, flipFrom]
      rw [flipNat_flipFrom j l, flipNat_flipFrom j r]

/-- Un passo del fan-out è un `CNOT` dal qubit `0`. -/
theorem cnotsFrom_step (j : Nat) {n : Nat} (l r : QState n) :
    cnotFrom0Nat (j + 1) (cnotsFrom (j + 2) (.node l r)) =
      cnotsFrom (j + 1) (.node l r) := by
  simp only [cnotFrom0Nat, cnotsFrom]
  rw [flipNat_flipFrom]

/-- Il controllo non è un bersaglio: `cnotsFrom 0` e `cnotsFrom 1` coincidono. -/
theorem cnots_skip_control {n : Nat} (l r : QState n) :
    cnotsFrom 0 (.node l r) = cnotsFrom 1 (.node l r) := rfl

/-- I `CNOT` dal sistema verso ogni altro qubit, su `|ψ⟩ ⊗ |0…0⟩`.

`ψ` sta sul qubit `0`. Gli altri qubit partono da `|0⟩`. -/
def fanout (ψ : Pair) : {n : Nat} → QState n
  | 0 => .leaf []
  | n + 1 => fanoutNat (embedAt ψ ⟨0, Nat.succ_pos n⟩ (ket0Q : QState n))

theorem norm_zero : {n : Nat} → normQ (zeroQ : QState n) = []
  | 0 => by simp only [zeroQ, normQ, columnBorn_nil]
  | _ + 1 => by
    simp only [zeroQ, normQ, norm_zero, List.append_nil]

theorem norm_onZero (z : Poly) : {n : Nat} → normQ (onZero z : QState n) = columnBorn z
  | 0 => rfl
  | _ + 1 => by
    simp only [onZero, normQ]
    rw [norm_onZero z, norm_zero, List.append_nil]

theorem norm_onOne (z : Poly) : {n : Nat} → normQ (onOne z : QState n) = columnBorn z
  | 0 => rfl
  | _ + 1 => by
    simp only [onOne, normQ]
    rw [norm_zero, norm_onOne z, List.nil_append]

theorem scale_zero (μ : Poly) : {n : Nat} → scaleQ μ (zeroQ : QState n) = zeroQ
  | 0 => by simp only [scaleQ, zeroQ, pmul_nil]
  | _ + 1 => by
    simp only [scaleQ, zeroQ, scale_zero]

theorem scale_onZero (μ : Poly) : {n : Nat} → scaleQ μ (ket0Q : QState n) = onZero μ
  | 0 => by
    simp only [scaleQ, ket0Q, onZero]
    rw [pmul_one]
  | _ + 1 => by
    simp only [scaleQ, ket0Q, onZero]
    rw [scale_onZero μ, scale_zero μ]

theorem scale_onOne (μ : Poly) : {n : Nat} → scaleQ μ (ket1Q : QState n) = onOne μ
  | 0 => by
    simp only [scaleQ, ket1Q, onOne]
    rw [pmul_one]
  | _ + 1 => by
    simp only [scaleQ, ket1Q, onOne]
    rw [scale_zero μ, scale_onOne μ]

theorem flip_zero : {n : Nat} → flipFrom 0 (zeroQ : QState n) = zeroQ
  | 0 => by simp only [flipFrom, zeroQ]
  | _ + 1 => by
    simp only [zeroQ, flipFrom, flip_zero]

theorem flip_ket0 : {n : Nat} → flipFrom 0 (ket0Q : QState n) = ket1Q
  | 0 => rfl
  | _ + 1 => by
    simp only [ket0Q, ket1Q, flipFrom]
    rw [flip_zero, flip_ket0]

theorem flip_scale (μ : Poly) : {n : Nat} → (v : QState n) →
    flipFrom 0 (scaleQ μ v) = scaleQ μ (flipFrom 0 v)
  | _, .leaf _ => rfl
  | _, .node l r => by
    simp only [flipFrom, scaleQ]
    rw [flip_scale μ r, flip_scale μ l]

/-- Il fan-out è `α|0…0⟩ + β|1…1⟩`. Ogni altra foglia è il polinomio zero. -/
theorem fanout_ghz (ψ : Pair) : {n : Nat} → (fanout ψ : QState n) = ghz ψ
  | 0 => rfl
  | _ + 1 => by
    simp only [fanout, fanoutNat, embedAt, cnotsFrom, ghz]
    rw [flip_scale, flip_ket0, scale_onZero, scale_onOne]

/-- Peso di Born sulle foglie in cui il qubit `k` vale `high`. -/
def bitBorn : Bool → Nat → {n : Nat} → QState n → Poly
  | _, _, 0, _ => []
  | false, 0, _ + 1, .node l _ => normQ l
  | true, 0, _ + 1, .node _ r => normQ r
  | high, j + 1, _ + 1, .node l r => bitBorn high j l ++ bitBorn high j r

/-- Peso di Born sulle foglie in cui il qubit `a` e il qubit `b` differiscono. -/
def disagreeBorn : Nat → Nat → {n : Nat} → QState n → Poly
  | _, _, 0, _ => []
  | 0, 0, _ + 1, _ => []
  | 0, j + 1, _ + 1, .node l r => bitBorn true j l ++ bitBorn false j r
  | i + 1, 0, _ + 1, .node l r => bitBorn true i l ++ bitBorn false i r
  | i + 1, j + 1, _ + 1, .node l r => disagreeBorn i j l ++ disagreeBorn i j r

theorem bitBorn_zero (high : Bool) (k : Nat) :
    {n : Nat} → bitBorn high k (zeroQ : QState n) = []
  | 0 => by simp only [bitBorn, zeroQ]
  | _ + 1 => by
    cases high <;> cases k <;>
      simp only [bitBorn, zeroQ, norm_zero, bitBorn_zero, List.append_nil]

theorem disagree_zero (a b : Nat) : {n : Nat} → disagreeBorn a b (zeroQ : QState n) = []
  | 0 => by simp only [disagreeBorn, zeroQ]
  | _ + 1 => by
    cases a <;> cases b <;>
      simp only [disagreeBorn, zeroQ, bitBorn_zero, disagree_zero, List.append_nil]

theorem bitBorn_onZero_one (k : Nat) (z : Poly) :
    {n : Nat} → k < n → bitBorn true k (onZero z : QState n) = []
  | 0, hk => absurd hk (Nat.not_lt_zero _)
  | _ + 1, hk =>
    match k with
    | 0 => by
      simp only [bitBorn, onZero]
      exact norm_zero
    | j + 1 => by
      simp only [bitBorn, onZero]
      rw [bitBorn_onZero_one j z (Nat.lt_of_succ_lt_succ hk), bitBorn_zero,
        List.append_nil]

theorem bitBorn_onOne_zero (k : Nat) (z : Poly) :
    {n : Nat} → k < n → bitBorn false k (onOne z : QState n) = []
  | 0, hk => absurd hk (Nat.not_lt_zero _)
  | _ + 1, hk =>
    match k with
    | 0 => by
      simp only [bitBorn, onOne]
      exact norm_zero
    | j + 1 => by
      simp only [bitBorn, onOne]
      rw [bitBorn_zero, bitBorn_onOne_zero j z (Nat.lt_of_succ_lt_succ hk),
        List.nil_append]

theorem disagree_onZero (a b : Nat) (h : a ≠ b) (z : Poly) :
    {n : Nat} → a < n → b < n → disagreeBorn a b (onZero z : QState n) = []
  | 0, ha, _ => absurd ha (Nat.not_lt_zero _)
  | _ + 1, ha, hb =>
    match a, b with
    | 0, 0 => absurd rfl h
    | 0, j + 1 => by
      simp only [onZero, disagreeBorn]
      rw [bitBorn_onZero_one j z (Nat.lt_of_succ_lt_succ hb), bitBorn_zero,
        List.append_nil]
    | i + 1, 0 => by
      simp only [onZero, disagreeBorn]
      rw [bitBorn_onZero_one i z (Nat.lt_of_succ_lt_succ ha), bitBorn_zero,
        List.append_nil]
    | i + 1, j + 1 => by
      simp only [onZero, disagreeBorn]
      rw [disagree_onZero i j (fun eq => h (congrArg Nat.succ eq)) z
          (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb),
        disagree_zero, List.append_nil]

theorem disagree_onOne (a b : Nat) (h : a ≠ b) (z : Poly) :
    {n : Nat} → a < n → b < n → disagreeBorn a b (onOne z : QState n) = []
  | 0, ha, _ => absurd ha (Nat.not_lt_zero _)
  | _ + 1, ha, hb =>
    match a, b with
    | 0, 0 => absurd rfl h
    | 0, j + 1 => by
      simp only [onOne, disagreeBorn]
      rw [bitBorn_zero, bitBorn_onOne_zero j z (Nat.lt_of_succ_lt_succ hb),
        List.append_nil]
    | i + 1, 0 => by
      simp only [onOne, disagreeBorn]
      rw [bitBorn_zero, bitBorn_onOne_zero i z (Nat.lt_of_succ_lt_succ ha),
        List.append_nil]
    | i + 1, j + 1 => by
      simp only [onOne, disagreeBorn]
      rw [disagree_zero, disagree_onOne i j (fun eq => h (congrArg Nat.succ eq)) z
          (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb),
        List.append_nil]

theorem disagree_ghz (a b : Nat) (h : a ≠ b) (ψ : Pair) :
    {n : Nat} → a < n → b < n → disagreeBorn a b (ghz ψ : QState n) = []
  | 0, ha, _ => absurd ha (Nat.not_lt_zero _)
  | _ + 1, ha, hb =>
    match a, b with
    | 0, 0 => absurd rfl h
    | 0, j + 1 => by
      simp only [ghz, disagreeBorn]
      rw [bitBorn_onZero_one j ψ.a0 (Nat.lt_of_succ_lt_succ hb),
        bitBorn_onOne_zero j ψ.a1 (Nat.lt_of_succ_lt_succ hb), List.append_nil]
    | i + 1, 0 => by
      simp only [ghz, disagreeBorn]
      rw [bitBorn_onZero_one i ψ.a0 (Nat.lt_of_succ_lt_succ ha),
        bitBorn_onOne_zero i ψ.a1 (Nat.lt_of_succ_lt_succ ha), List.append_nil]
    | i + 1, j + 1 => by
      simp only [ghz, disagreeBorn]
      rw [disagree_onZero i j (fun eq => h (congrArg Nat.succ eq)) ψ.a0
          (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb),
        disagree_onOne i j (fun eq => h (congrArg Nat.succ eq)) ψ.a1
          (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb),
        List.append_nil]

/-- Due qubit del fan-out non discordano.

La somma dei pesi di Born sulle celle in cui differiscono è il
polinomio zero. Gli osservatori sono i qubit diversi dal sistema, e
il sistema è il qubit `0`: la coppia è una coppia qualsiasi. -/
theorem fanout_agree {n : Nat} (a b : Fin n) (h : a ≠ b) (ψ : Pair) :
    disagreeBorn a.val b.val (fanout ψ : QState n) = [] := by
  rw [fanout_ghz]
  exact disagree_ghz a.val b.val (Fin.val_ne_of_ne h) ψ a.isLt b.isLt

theorem zipCoh_zero_right : {n : Nat} → (v : QState n) → zipCoh v zeroQ = []
  | _, .leaf _ => by simp only [zipCoh, zeroQ, conjP, pmul_nil]
  | _, .node l r => by
    simp only [zipCoh, zeroQ]
    rw [zipCoh_zero_right l, zipCoh_zero_right r, List.append_nil]

theorem zipCoh_zero_left : {n : Nat} → (v : QState n) → zipCoh zeroQ v = []
  | _, .leaf _ => by simp only [zipCoh, zeroQ, pmul_nil_left]
  | _, .node l r => by
    simp only [zipCoh, zeroQ]
    rw [zipCoh_zero_left l, zipCoh_zero_left r, List.append_nil]

theorem zipCoh_on_split (α β : Poly) {n : Nat} :
    zipCoh (onZero α : QState (n + 1)) (onOne β) = [] := by
  simp only [onZero, onOne, zipCoh]
  rw [zipCoh_zero_right, zipCoh_zero_left, List.append_nil]

theorem zipCoh_on_split_rev (α β : Poly) {n : Nat} :
    zipCoh (onOne β : QState (n + 1)) (onZero α) = [] := by
  simp only [onZero, onOne, zipCoh]
  rw [zipCoh_zero_left, zipCoh_zero_right, List.append_nil]

/-- Per `n ≥ 2` il sistema, il qubit `0`, è diagonale con `bornPair ψ`. -/
theorem fanout_decoherence {n : Nat} (ψ : Pair) :
    reduceAt ⟨0, Nat.succ_pos (n + 1)⟩ (fanout ψ : QState (n + 2)) =
      ⟨(bornPair ψ).a0, [], [], (bornPair ψ).a1⟩ := by
  rw [fanout_ghz]
  simp only [ghz, reduceAt, reduceNat]
  exact Mat.ext (norm_onZero ψ.a0) (zipCoh_on_split ψ.a0 ψ.a1)
    (zipCoh_on_split_rev ψ.a0 ψ.a1) (norm_onOne ψ.a1)

end Universe.Qubits
