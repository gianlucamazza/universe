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
-/
import Universe.Composition
import Universe.Epistemology

namespace Universe.Qubits

open Universe.Composition
open Universe.Dynamics
open Universe.Epistemology
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

end Universe.Qubits
