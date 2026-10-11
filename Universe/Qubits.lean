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
-/
import Universe.Epistemology

namespace Universe.Qubits

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

end Universe.Qubits
