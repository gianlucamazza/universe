/-
Istanza di `Universe.Series.expCoeff` sull'Hamiltoniana del qubit.

`H² = I` vale nel quoziente `|n| = 1`, non come uguaglianza di liste.
Il carrier di `qubitDyn` è il quoziente delle matrici, quindi `HQ * HQ = 1`
è l'ipotesi di `expCoeff`. Quel teorema autorizza la forma chiusa
`U = c I − i s H` usata dal kernel Python: i coefficienti di `φⁿ/n!` coincidono.
`c` e `s` restano indeterminate del quoziente `c² + s² = 1`; non sono la serie.

`evolution_unitary` è `U†U = I` nello stesso quoziente.
`evolved_on_sphere` è `‖Uψ‖² − 1` nell'ideale `(gC, gN, gA)`.
-/
import Universe.Dynamics
import Universe.Series

namespace Universe.Qubit

open Universe.Ring
open Universe.Series
open Universe.Quotient hiding mul
open Universe.Dynamics

def c1 : Mono := {Mono.one with c := 1}
def s1 : Mono := {Mono.one with s := 1}
def nx1 : Mono := {Mono.one with nx := 1}
def ny1 : Mono := {Mono.one with ny := 1}
def nz1 : Mono := {Mono.one with nz := 1}
def ar1 : Mono := {Mono.one with ar := 1}
def ai1 : Mono := {Mono.one with ai := 1}
def br1 : Mono := {Mono.one with br := 1}
def bi1 : Mono := {Mono.one with bi := 1}

/-- `n·σ`, la stessa matrice del kernel Python. -/
def hamiltonian : Mat where
  a00 := single 1 nz1
  a01 := single 1 nx1 ++ single (-Gauss.i) ny1
  a10 := single 1 nx1 ++ single Gauss.i ny1
  a11 := single (-1) nz1

/-- `c I − i s H`. -/
def evolution : Mat where
  a00 := single 1 c1 ++ single (-Gauss.i) (s1.mul nz1)
  a01 := single (-1) (s1.mul ny1) ++ single (-Gauss.i) (s1.mul nx1)
  a10 := single 1 (s1.mul ny1) ++ single (-Gauss.i) (s1.mul nx1)
  a11 := single 1 c1 ++ single Gauss.i (s1.mul nz1)

def generic0 : Poly := single 1 ar1 ++ single Gauss.i ai1
def generic1 : Poly := single 1 br1 ++ single Gauss.i bi1

/-- `‖Uψ‖²` per lo stato generico, nell'anello libero. -/
def evolvedNorm : Poly :=
  let v0 := pmul evolution.a00 generic0 ++ pmul evolution.a01 generic1
  let v1 := pmul evolution.a10 generic0 ++ pmul evolution.a11 generic1
  pmul v0 (conjP v0) ++ pmul v1 (conjP v1)

/-- Appartenenza all'ideale `(gC, gN, gA)`. -/
def inIdealA (p : Poly) : Prop :=
  ∃ fc fn fa, ∀ t,
    coeffOf p t = coeffOf (pmul fc gC ++ pmul fn gN ++ pmul fa gA) t

theorem polySame_support {p q : Poly}
    (h : ∀ m, m ∈ support (p ++ q) → coeffOf p m = coeffOf q m) : polySame p q := by
  intro t
  by_cases ht : t ∈ support (p ++ q)
  · exact h t ht
  · have hp : t ∉ support p := fun hm => ht ((mem_support_append p q t).2 (Or.inl hm))
    have hq : t ∉ support q := fun hm => ht ((mem_support_append p q t).2 (Or.inr hm))
    rw [not_support_coeff p t hp, not_support_coeff q t hq]

private def axisSq : Poly := single 1 nxSq ++ single 1 nySq ++ single 1 nzSq

private theorem polySame_psub_one (p : Poly) :
    polySame (psub p (single 1 Mono.one)) (p ++ single (-1) Mono.one) := by
  intro t
  rw [coeff_psub, coeffOf_append, coeff_single_eq, coeff_single_eq]
  by_cases ht : Mono.one = t
  · simp [ht]
  · simp [ht, Gauss.neg_zero]

private theorem ideal_of_axis (p : Poly) (h : polySame p axisSq) :
    inIdeal (psub p (single 1 Mono.one)) := by
  have htail : polySame (p ++ single (-1) Mono.one) gN := by
    have hg : axisSq ++ single (-1) Mono.one = gN := rfl
    rw [← hg]
    exact polySame_append h (polySame_refl _)
  exact inIdeal_polySame ((polySame_psub_one p).trans htail) inIdeal_gN

private theorem ideal_of_zero (p : Poly) (h : polySame p []) : inIdeal (psub p []) :=
  inIdeal_of_polySame h

private theorem diag_00 :
    polySame (matMul hamiltonian hamiltonian).a00 axisSq := by
  refine polySame_support ?_
  native_decide

private theorem diag_11 :
    polySame (matMul hamiltonian hamiltonian).a11 axisSq := by
  refine polySame_support ?_
  native_decide

private theorem off_01 :
    polySame (matMul hamiltonian hamiltonian).a01 [] := by
  refine polySame_support ?_
  native_decide

private theorem off_10 :
    polySame (matMul hamiltonian hamiltonian).a10 [] := by
  refine polySame_support ?_
  native_decide

theorem hamiltonian_sq : matRel (matMul hamiltonian hamiltonian) matOne :=
  ⟨ideal_of_axis _ diag_00, ideal_of_zero _ off_01, ideal_of_zero _ off_10,
    ideal_of_axis _ diag_11⟩

def HQ : QMat := Quotient.mk matSetoid hamiltonian

theorem HQ_sq : qubitDyn.mul HQ HQ = qubitDyn.one := by
  change Quotient.mk matSetoid (matMul hamiltonian hamiltonian) = Quotient.mk matSetoid matOne
  exact Quotient.sound hamiltonian_sq

/-- Istanza di `expCoeff` su `H`. Autorizza `U = c I − i s H`. -/
theorem expCoeff_hamiltonian (n : Nat) :
    expSeries qubitDyn HQ n = closedSeries qubitDyn HQ n :=
  expCoeff qubitDyn HQ HQ_sq n

theorem expSeries_hamiltonian :
    expSeries qubitDyn HQ = closedSeries qubitDyn HQ :=
  expSeries_eq_closed qubitDyn HQ HQ_sq

private def unitaryDefect : Poly := gC ++ pmul (single 1 sSq) gN

private theorem unitary_ideal : inIdeal unitaryDefect :=
  inIdeal_append inIdeal_gC (inIdeal_mul_left (single 1 sSq) inIdeal_gN)

private theorem unitary_00 :
    polySame (psub (matMul (matDagger evolution) evolution).a00 (single 1 Mono.one))
      unitaryDefect := by
  refine polySame_support ?_
  native_decide

private theorem unitary_11 :
    polySame (psub (matMul (matDagger evolution) evolution).a11 (single 1 Mono.one))
      unitaryDefect := by
  refine polySame_support ?_
  native_decide

private theorem unitary_01 :
    polySame (matMul (matDagger evolution) evolution).a01 [] := by
  refine polySame_support ?_
  native_decide

private theorem unitary_10 :
    polySame (matMul (matDagger evolution) evolution).a10 [] := by
  refine polySame_support ?_
  native_decide

theorem evolution_unitary : matRel (matMul (matDagger evolution) evolution) matOne :=
  ⟨inIdeal_polySame unitary_00 unitary_ideal, ideal_of_zero _ unitary_01,
    ideal_of_zero _ unitary_10, inIdeal_polySame unitary_11 unitary_ideal⟩

private def sphereCombo : Poly :=
  pmul amp gC ++ pmul (pmul (single 1 sSq) amp) gN ++ pmul (single 1 Mono.one) gA

theorem evolved_sphere_coeffs :
    polySame (psub evolvedNorm (single 1 Mono.one)) sphereCombo := by
  refine polySame_support ?_
  native_decide

/-- `‖Uψ‖² − 1` sta in `(gC, gN, gA)`. Sulla sfera il resto è zero. -/
theorem evolved_on_sphere : inIdealA (psub evolvedNorm (single 1 Mono.one)) :=
  ⟨amp, pmul (single 1 sSq) amp, single 1 Mono.one, fun t => evolved_sphere_coeffs t⟩

end Universe.Qubit
