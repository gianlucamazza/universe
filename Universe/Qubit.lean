/-
Istanza di `Universe.Series.expCoeff` sull'Hamiltoniana del qubit.

`H = n·σ` con `Y = [[0, −i], [i, 0]]`. Nel quoziente `|n| = 1` la diagonale di
`H² − I` è `gN` (cofattore 1) e il fuori diagonale ha coefficienti zero.
`HQ * HQ = 1` è l'ipotesi di `expCoeff`: i coefficienti di `φⁿ/n!` in
`exp(−i φ H)` sono quelli di `cos φ · I + (−i sin φ) · H`.
`U = c I − i s H`. `U†U`, `UU†` e `det U − 1` hanno gli stessi cofattori
`gC + s² gN`. Per ogni ampiezza, `ψ† (U†U) ψ − ‖ψ‖²` sta in quell'ideale.
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

def h00 : Poly := single 1 nz1
def h01 : Poly := single 1 nx1 ++ single (-Gauss.i) ny1
def h10 : Poly := single 1 nx1 ++ single Gauss.i ny1
def h11 : Poly := single (-1) nz1

/-- `n·σ`. -/
def hamiltonian : Mat := ⟨h00, h01, h10, h11⟩

def sigmaX : Mat := ⟨[], single 1 Mono.one, single 1 Mono.one, []⟩
def sigmaY : Mat := ⟨[], single (-Gauss.i) Mono.one, single Gauss.i Mono.one, []⟩
def sigmaZ : Mat := ⟨single 1 Mono.one, [], [], single (-1) Mono.one⟩

def pauliHamiltonian : Mat :=
  matAdd (matAdd (matScale (single 1 nx1) sigmaX) (matScale (single 1 ny1) sigmaY))
    (matScale (single 1 nz1) sigmaZ)

def cP : Poly := single 1 c1
def gamma : Poly := single (-Gauss.i) s1

/-- `p I + q H`, prodotto a sinistra sulle entrate. -/
def lin (p q : Poly) (H : Mat) : Mat where
  a00 := pmul p (single 1 Mono.one) ++ pmul q H.a00
  a01 := pmul q H.a01
  a10 := pmul q H.a10
  a11 := pmul p (single 1 Mono.one) ++ pmul q H.a11

/-- `U = c I − i s H`. -/
def evolution : Mat := lin cP gamma hamiltonian

def axisSq : Poly := single 1 nxSq ++ single 1 nySq ++ single 1 nzSq

def unitaryDefect : Poly := gC ++ pmul (single 1 sSq) gN

theorem h11_neg : h11 = pneg h00 := rfl

theorem nx1_sq : nx1.mul nx1 = nxSq := rfl
theorem ny1_sq : ny1.mul ny1 = nySq := rfl
theorem nz1_sq : nz1.mul nz1 = nzSq := rfl
theorem s1_sq : s1.mul s1 = sSq := rfl
theorem c1_sq : c1.mul c1 = cSq := rfl
theorem axis_tail : axisSq ++ single (-1) Mono.one = gN := rfl

theorem minus_i_sq : (-Gauss.i) * -Gauss.i = -1 := by
  rw [← Gauss.neg_mul, Gauss.mul_neg, Gauss.neg_neg, Gauss.i_mul_i]

theorem neg_one_sq : (-1 : Gauss) * -1 = 1 := by
  rw [Gauss.neg_one_mul, Gauss.neg_neg]

theorem conjP_real (m : Mono) : conjP (single (1 : Gauss) m) = single 1 m := by
  rw [show conjP (single (1 : Gauss) m) = single (Gauss.conj 1) m from rfl, conj_one]

theorem conjP_imag (m : Mono) : conjP (single Gauss.i m) = single (-Gauss.i) m := by
  rw [show conjP (single Gauss.i m) = single (Gauss.conj Gauss.i) m from rfl, conj_i]

theorem conjP_neg_imag (m : Mono) : conjP (single (-Gauss.i) m) = single Gauss.i m := by
  rw [show conjP (single (-Gauss.i) m) = single (Gauss.conj (-Gauss.i)) m from rfl, conj_neg_i]

theorem conjP_neg_one (m : Mono) : conjP (single (-1 : Gauss) m) = single (-1) m := by
  rw [show conjP (single (-1) m) = single (Gauss.conj (-1)) m from rfl]
  rw [show Gauss.conj (-1 : Gauss) = -1 by rw [conj_neg, conj_one]]

theorem hamiltonian_dagger : matDagger hamiltonian = hamiltonian := by
  apply Mat.ext
  · rw [show (matDagger hamiltonian).a00 = conjP h00 from rfl, h00, conjP_real, hamiltonian, h00]
  · rw [show (matDagger hamiltonian).a01 = conjP h10 from rfl, h10, conj_append, conjP_real,
      conjP_imag, hamiltonian, h01]
  · rw [show (matDagger hamiltonian).a10 = conjP h01 from rfl, h01, conj_append, conjP_real,
      conjP_neg_imag, hamiltonian, h10]
  · rw [show (matDagger hamiltonian).a11 = conjP h11 from rfl, h11, conjP_neg_one, hamiltonian,
      h11]

theorem hamiltonian_pauli : hamiltonian = pauliHamiltonian := by
  apply Mat.ext
  · simp only [hamiltonian, pauliHamiltonian, matAdd, matScale, sigmaX, sigmaY, sigmaZ, h00]
    rw [pmul_nil, pmul_nil, pmul_one, List.nil_append, List.nil_append]
  · simp only [hamiltonian, pauliHamiltonian, matAdd, matScale, sigmaX, sigmaY, sigmaZ, h01]
    rw [pmul_one, pmul_nil, pmul_single_single, Gauss.one_mul, Mono.mul_one, List.append_nil,
      List.append_nil]
  · simp only [hamiltonian, pauliHamiltonian, matAdd, matScale, sigmaX, sigmaY, sigmaZ, h10]
    rw [pmul_one, pmul_nil, pmul_single_single, Gauss.one_mul, Mono.mul_one, List.append_nil,
      List.append_nil]
  · simp only [hamiltonian, pauliHamiltonian, matAdd, matScale, sigmaX, sigmaY, sigmaZ, h11]
    rw [pmul_nil, pmul_nil, pmul_single_single, Gauss.one_mul, Mono.mul_one]
    rw [List.append_nil (single (-1) nz1), List.nil_append, List.nil_append]

theorem coeff_single_mul (a b : Gauss) (m n t : Mono) :
    coeffOf (pmul (single a m) (single b n)) t = if m.mul n = t then a * b else 0 := by
  rw [pmul_single_single, coeffOf_append, coeff_single_eq, coeffOf_nil, Gauss.add_zero]

theorem coeff_dist4 (p q r s : Poly) (t : Mono) :
    coeffOf (pmul (p ++ q) (r ++ s)) t =
      (coeffOf (pmul p r) t + coeffOf (pmul p s) t) +
        (coeffOf (pmul q r) t + coeffOf (pmul q s) t) := by
  rw [pmul_append_left, coeffOf_append, coeff_mul_append_right, coeff_mul_append_right,
    coeffOf_append, coeffOf_append]

theorem cross_cancel (m t : Mono) :
    (if m = t then Gauss.i else 0) + (if m = t then -Gauss.i else 0) = 0 := by
  by_cases h : m = t
  · rw [ite_eq_left h, ite_eq_left h, Gauss.add_neg_cancel]
  · rw [ite_eq_right h, ite_eq_right h, Gauss.zero_add]

theorem coeff_h01_h10 (t : Mono) :
    coeffOf (pmul h01 h10) t = coeffOf (single (1 : Gauss) nxSq ++ single 1 nySq) t := by
  rw [h01, h10, coeff_dist4, coeff_single_mul, coeff_single_mul, coeff_single_mul,
    coeff_single_mul, nx1_sq, ny1_sq, Mono.mul_comm ny1 nx1]
  rw [Gauss.mul_one, Gauss.mul_one, Gauss.one_mul, minus_i_mul_i]
  rw [coeffOf_append, coeff_single_eq, coeff_single_eq]
  rw [Gauss.add_assoc]
  rw [← Gauss.add_assoc (if nx1.mul ny1 = t then Gauss.i else 0)
      (if nx1.mul ny1 = t then -Gauss.i else 0) (if nySq = t then 1 else 0)]
  rw [cross_cancel (nx1.mul ny1) t, Gauss.zero_add]

theorem coeff_nz_sq (t : Mono) :
    coeffOf (pmul h00 h00) t = coeffOf (single 1 nzSq) t := by
  rw [h00, coeff_single_mul, nz1_sq, Gauss.mul_one, coeff_single_eq]

theorem coeff_h11_sq (t : Mono) :
    coeffOf (pmul h11 h11) t = coeffOf (single 1 nzSq) t := by
  rw [h11, coeff_single_mul, nz1_sq, neg_one_sq, coeff_single_eq]

theorem coeff_h2_00 (t : Mono) :
    coeffOf (matMul hamiltonian hamiltonian).a00 t = coeffOf axisSq t := by
  rw [show (matMul hamiltonian hamiltonian).a00 = pmul h00 h00 ++ pmul h01 h10 from rfl]
  rw [coeffOf_append, coeff_nz_sq, coeff_h01_h10, axisSq]
  rw [coeffOf_append (single 1 nxSq ++ single 1 nySq) (single 1 nzSq)]
  exact Gauss.add_comm _ _

theorem coeff_h2_11 (t : Mono) :
    coeffOf (matMul hamiltonian hamiltonian).a11 t = coeffOf axisSq t := by
  rw [show (matMul hamiltonian hamiltonian).a11 = pmul h10 h01 ++ pmul h11 h11 from rfl]
  rw [coeffOf_append, coeff_mul_comm, coeff_h01_h10, coeff_h11_sq, axisSq]
  rw [coeffOf_append (single 1 nxSq ++ single 1 nySq) (single 1 nzSq)]

theorem coeff_h2_01 (t : Mono) :
    coeffOf (matMul hamiltonian hamiltonian).a01 t = 0 := by
  rw [show (matMul hamiltonian hamiltonian).a01 = pmul h00 h01 ++ pmul h01 h11 from rfl, h11_neg,
    coeffOf_append, coeff_pmul_pneg_right, coeff_mul_comm, Gauss.add_neg_cancel]

theorem coeff_h2_10 (t : Mono) :
    coeffOf (matMul hamiltonian hamiltonian).a10 t = 0 := by
  rw [show (matMul hamiltonian hamiltonian).a10 = pmul h10 h00 ++ pmul h11 h10 from rfl, h11_neg,
    coeffOf_append, ← pneg_pmul, coeff_pneg, coeff_mul_comm, Gauss.add_neg_cancel]

theorem polySame_psub_one (p : Poly) :
    polySame (psub p (single 1 Mono.one)) (p ++ single (-1) Mono.one) := by
  intro t
  rw [coeff_psub, coeffOf_append, coeff_single_eq, coeff_single_eq]
  by_cases ht : Mono.one = t
  · rw [ite_eq_left ht, ite_eq_left ht]
  · rw [ite_eq_right ht, ite_eq_right ht, Gauss.neg_zero, Gauss.add_zero]

theorem ideal_of_axis (p : Poly) (h : polySame p axisSq) :
    inIdeal (psub p (single 1 Mono.one)) := by
  have htail : polySame (p ++ single (-1) Mono.one) gN := by
    rw [← axis_tail]
    exact polySame_append h (polySame_refl _)
  exact inIdeal_polySame (polySame.trans (polySame_psub_one p) htail) inIdeal_gN

theorem ideal_of_zero (p : Poly) (h : polySame p []) : inIdeal (psub p []) :=
  inIdeal_of_polySame h

theorem diag_00 : polySame (matMul hamiltonian hamiltonian).a00 axisSq := coeff_h2_00

theorem diag_11 : polySame (matMul hamiltonian hamiltonian).a11 axisSq := coeff_h2_11

theorem off_01 : polySame (matMul hamiltonian hamiltonian).a01 [] := by
  intro t
  rw [coeff_h2_01, coeffOf_nil]

theorem off_10 : polySame (matMul hamiltonian hamiltonian).a10 [] := by
  intro t
  rw [coeff_h2_10, coeffOf_nil]

/-- Diagonale: cofattore `gN`. Fuori diagonale: coefficienti zero. -/
theorem hamiltonian_sq : matRel (matMul hamiltonian hamiltonian) matOne :=
  ⟨ideal_of_axis _ diag_00, ideal_of_zero _ off_01, ideal_of_zero _ off_10,
    ideal_of_axis _ diag_11⟩

def HQ : QMat := Quotient.mk matSetoid hamiltonian

theorem HQ_sq : qubitDyn.mul HQ HQ = qubitDyn.one := by
  have hmul : qubitDyn.mul = qmul := by unfold qubitDyn; rfl
  have hone : qubitDyn.one = Quotient.mk matSetoid matOne := by unfold qubitDyn; rfl
  rw [hmul, hone, HQ, qmul_mk]
  exact Quotient.sound hamiltonian_sq

/-- `H³ = H`, per moltiplicazione da `H² = I`. -/
theorem hamiltonian_cube : qubitDyn.mul (qubitDyn.mul HQ HQ) HQ = HQ := by
  rw [HQ_sq, qubitDyn.one_mul]

/-- `H⁴ = I`, per moltiplicazione da `H² = I`. -/
theorem hamiltonian_fourth :
    qubitDyn.mul (qubitDyn.mul HQ HQ) (qubitDyn.mul HQ HQ) = qubitDyn.one := by
  rw [HQ_sq, qubitDyn.one_mul]

/-- Istanza di `expCoeff` su `H`. Autorizza `U = c I − i s H`. -/
theorem expCoeff_hamiltonian (n : Nat) :
    expSeries qubitDyn HQ n = closedSeries qubitDyn HQ n :=
  expCoeff qubitDyn HQ HQ_sq n

theorem expSeries_hamiltonian : expSeries qubitDyn HQ = closedSeries qubitDyn HQ :=
  expSeries_eq_closed qubitDyn HQ HQ_sq

/-! ### Unità di `U` -/

theorem conjP_gamma : conjP gamma = pneg gamma := by
  rw [gamma]
  rw [show conjP (single (-Gauss.i) s1) = single (Gauss.conj (-Gauss.i)) s1 from rfl, conj_neg_i]
  rfl

theorem matDagger_lin (p q : Poly) (H : Mat) (hp : conjP p = p) (hq : conjP q = pneg q)
    (hH : matDagger H = H) : matDagger (lin p q H) = lin p (pneg q) H := by
  have h0 : conjP H.a00 = H.a00 := by rw [← show (matDagger H).a00 = conjP H.a00 from rfl, hH]
  have h1 : conjP H.a11 = H.a11 := by rw [← show (matDagger H).a11 = conjP H.a11 from rfl, hH]
  have h01 : conjP H.a10 = H.a01 := by rw [← show (matDagger H).a01 = conjP H.a10 from rfl, hH]
  have h10 : conjP H.a01 = H.a10 := by rw [← show (matDagger H).a10 = conjP H.a01 from rfl, hH]
  apply Mat.ext
  · rw [show (matDagger (lin p q H)).a00 = conjP (lin p q H).a00 from rfl, lin, conj_append,
      conj_pmul, conj_pmul, hp, hq, h0, conjP_real, lin]
  · rw [show (matDagger (lin p q H)).a01 = conjP (lin p q H).a10 from rfl, lin, conj_pmul, hq, h01,
      lin]
  · rw [show (matDagger (lin p q H)).a10 = conjP (lin p q H).a01 from rfl, lin, conj_pmul, hq, h10,
      lin]
  · rw [show (matDagger (lin p q H)).a11 = conjP (lin p q H).a11 from rfl, lin, conj_append,
      conj_pmul, conj_pmul, hp, hq, h1, conjP_real, lin]

theorem evolution_dagger : matDagger evolution = lin cP (pneg gamma) hamiltonian := by
  rw [evolution, matDagger_lin cP gamma hamiltonian conjP_real_c conjP_gamma hamiltonian_dagger]
where
  conjP_real_c : conjP cP = cP := by rw [cP, conjP_real]

theorem coeff_slide_cancel (p q a : Poly) (t : Mono) :
    coeffOf (pmul p (pmul q a)) t + coeffOf (pmul (pmul (pneg q) a) p) t = 0 := by
  have hleft : polySame (pmul p (pneg q)) (pneg (pmul p q)) := by
    intro u
    rw [coeff_pmul_pneg_right, coeff_pneg]
  calc
    coeffOf (pmul p (pmul q a)) t + coeffOf (pmul (pmul (pneg q) a) p) t
        = coeffOf (pmul p (pmul q a)) t + coeffOf (pmul p (pmul (pneg q) a)) t := by
          rw [coeff_mul_comm (pmul (pneg q) a) p]
    _ = coeffOf (pmul (pmul p q) a) t + coeffOf (pmul (pmul p (pneg q)) a) t := by
          rw [← pmul_assoc, ← pmul_assoc]
    _ = coeffOf (pmul (pmul p q) a) t + coeffOf (pmul (pneg (pmul p q)) a) t := by
          rw [coeff_mul_congr_left hleft]
    _ = coeffOf (pmul (pmul p q) a) t + -coeffOf (pmul (pmul p q) a) t := by
          rw [← pneg_pmul, coeff_pneg]
    _ = 0 := Gauss.add_neg_cancel _

theorem polySame_assoc_comm (a b c d : Poly) :
    polySame (pmul (pmul a b) (pmul c d)) (pmul (pmul a c) (pmul b d)) := by
  intro t
  calc
    coeffOf (pmul (pmul a b) (pmul c d)) t
        = coeffOf (pmul a (pmul b (pmul c d))) t := by rw [pmul_assoc a b (pmul c d)]
    _ = coeffOf (pmul a (pmul (pmul b c) d)) t := by rw [← pmul_assoc b c d]
    _ = coeffOf (pmul a (pmul (pmul c b) d)) t := by
          rw [coeff_mul_congr_right
            (fun u => coeff_mul_congr_left (coeff_mul_comm b c) d u) a t]
    _ = coeffOf (pmul (pmul a (pmul c b)) d) t := by rw [← pmul_assoc a (pmul c b) d]
    _ = coeffOf (pmul (pmul (pmul a c) b) d) t := by rw [← pmul_assoc a c b]
    _ = coeffOf (pmul (pmul a c) (pmul b d)) t := by rw [pmul_assoc (pmul a c) b d]

theorem coeff_scale_sum (s a b : Poly) (t : Mono) :
    coeffOf (pmul s a) t + coeffOf (pmul s b) t = coeffOf (pmul s (a ++ b)) t := by
  rw [← coeffOf_append, ← coeff_mul_append_right]

theorem gamma_factor (t : Mono) :
    coeffOf (pmul (pneg gamma) gamma) t = coeffOf (single 1 sSq) t := by
  have hsq : coeffOf (pmul gamma gamma) t = coeffOf (single (-1) sSq) t := by
    rw [gamma, coeff_single_mul, s1_sq, minus_i_sq, coeff_single_eq]
  rw [← pneg_pmul, coeff_pneg, hsq, coeff_single_eq, coeff_single_eq]
  by_cases h : sSq = t
  · rw [ite_eq_left h, ite_eq_left h, Gauss.neg_neg]
  · rw [ite_eq_right h, ite_eq_right h, Gauss.neg_zero]

def scalarμ : Poly := pmul cP cP ++ pmul (single 1 sSq) axisSq

theorem coeff_axis_scaled (t : Mono) :
    coeffOf (pmul (pmul (pneg gamma) h00) (pmul gamma h00)) t +
        coeffOf (pmul (pmul (pneg gamma) h01) (pmul gamma h10)) t =
      coeffOf (pmul (single 1 sSq) axisSq) t := by
  have h0 := polySame_assoc_comm (pneg gamma) h00 gamma h00 t
  have h1 := polySame_assoc_comm (pneg gamma) h01 gamma h10 t
  rw [h0, h1, coeff_scale_sum]
  rw [show pmul h00 h00 ++ pmul h01 h10 = (matMul hamiltonian hamiltonian).a00 from rfl]
  rw [coeff_mul_congr_right diag_00, coeff_mul_congr_left gamma_factor]

theorem coeff_axis_scaled_11 (t : Mono) :
    coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h11)) t +
        coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h01)) t =
      coeffOf (pmul (single 1 sSq) axisSq) t := by
  have h0 := polySame_assoc_comm (pneg gamma) h11 gamma h11 t
  have h1 := polySame_assoc_comm (pneg gamma) h10 gamma h01 t
  have hswap : polySame (pmul h11 h11 ++ pmul h10 h01) (pmul h10 h01 ++ pmul h11 h11) := by
    intro u
    rw [coeffOf_append, coeffOf_append, Gauss.add_comm]
  rw [h0, h1, coeff_scale_sum, coeff_mul_congr_right hswap]
  rw [show pmul h10 h01 ++ pmul h11 h11 = (matMul hamiltonian hamiltonian).a11 from rfl]
  rw [coeff_mul_congr_right diag_11, coeff_mul_congr_left gamma_factor]

theorem coeff_off_scaled (t : Mono) :
    coeffOf (pmul (pmul (pneg gamma) h00) (pmul gamma h01)) t +
        coeffOf (pmul (pmul (pneg gamma) h01) (pmul gamma h11)) t = 0 := by
  have h0 := polySame_assoc_comm (pneg gamma) h00 gamma h01 t
  have h1 := polySame_assoc_comm (pneg gamma) h01 gamma h11 t
  rw [h0, h1, coeff_scale_sum]
  rw [show pmul h00 h01 ++ pmul h01 h11 = (matMul hamiltonian hamiltonian).a01 from rfl]
  rw [coeff_mul_congr_right off_01, pmul_nil, coeffOf_nil]

theorem coeff_off_scaled_10 (t : Mono) :
    coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h10)) t +
        coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h00)) t = 0 := by
  have h0 := polySame_assoc_comm (pneg gamma) h11 gamma h10 t
  have h1 := polySame_assoc_comm (pneg gamma) h10 gamma h00 t
  have hswap : polySame (pmul h11 h10 ++ pmul h10 h00) (pmul h10 h00 ++ pmul h11 h10) := by
    intro u
    rw [coeffOf_append, coeffOf_append, Gauss.add_comm]
  rw [h0, h1, coeff_scale_sum, coeff_mul_congr_right hswap]
  rw [show pmul h10 h00 ++ pmul h11 h10 = (matMul hamiltonian hamiltonian).a10 from rfl]
  rw [coeff_mul_congr_right off_10, pmul_nil, coeffOf_nil]

theorem evolution_diag_00 (t : Mono) :
    coeffOf (matMul (matDagger evolution) evolution).a00 t = coeffOf scalarμ t := by
  rw [evolution_dagger, evolution]
  have hentry :
      (matMul (lin cP (pneg gamma) hamiltonian) (lin cP gamma hamiltonian)).a00 =
        pmul (cP ++ pmul (pneg gamma) h00) (cP ++ pmul gamma h00) ++
          pmul (pmul (pneg gamma) h01) (pmul gamma h10) := by
    unfold matMul lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  rw [hentry, scalarμ]
  calc
    coeffOf (pmul (cP ++ pmul (pneg gamma) h00) (cP ++ pmul gamma h00) ++
        pmul (pmul (pneg gamma) h01) (pmul gamma h10)) t
        = ((coeffOf (pmul cP cP) t + coeffOf (pmul cP (pmul gamma h00)) t) +
            (coeffOf (pmul (pmul (pneg gamma) h00) cP) t +
              coeffOf (pmul (pmul (pneg gamma) h00) (pmul gamma h00)) t)) +
            coeffOf (pmul (pmul (pneg gamma) h01) (pmul gamma h10)) t := by
          rw [coeffOf_append, coeff_dist4]
    _ = ((coeffOf (pmul cP cP) t +
          coeffOf (pmul (pmul (pneg gamma) h00) (pmul gamma h00)) t) +
          (coeffOf (pmul cP (pmul gamma h00)) t +
            coeffOf (pmul (pmul (pneg gamma) h00) cP) t)) +
          coeffOf (pmul (pmul (pneg gamma) h01) (pmul gamma h10)) t := by
          rw [Gauss.add_comm
              (coeffOf (pmul (pmul (pneg gamma) h00) cP) t)
              (coeffOf (pmul (pmul (pneg gamma) h00) (pmul gamma h00)) t),
            Gauss.add_add_add_comm]
    _ = (coeffOf (pmul cP cP) t +
          coeffOf (pmul (pmul (pneg gamma) h00) (pmul gamma h00)) t) +
          coeffOf (pmul (pmul (pneg gamma) h01) (pmul gamma h10)) t := by
          rw [coeff_slide_cancel cP gamma h00, Gauss.add_zero]
    _ = coeffOf (pmul cP cP) t + coeffOf (pmul (single 1 sSq) axisSq) t := by
          rw [Gauss.add_assoc, coeff_axis_scaled]
    _ = coeffOf (pmul cP cP ++ pmul (single 1 sSq) axisSq) t := by
          rw [← coeffOf_append]

theorem evolution_diag_11 (t : Mono) :
    coeffOf (matMul (matDagger evolution) evolution).a11 t = coeffOf scalarμ t := by
  rw [evolution_dagger, evolution]
  have hentry :
      (matMul (lin cP (pneg gamma) hamiltonian) (lin cP gamma hamiltonian)).a11 =
        pmul (pmul (pneg gamma) h10) (pmul gamma h01) ++
          pmul (cP ++ pmul (pneg gamma) h11) (cP ++ pmul gamma h11) := by
    unfold matMul lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  rw [hentry, scalarμ]
  calc
    coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h01) ++
        pmul (cP ++ pmul (pneg gamma) h11) (cP ++ pmul gamma h11)) t
        = coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h01)) t +
            ((coeffOf (pmul cP cP) t + coeffOf (pmul cP (pmul gamma h11)) t) +
              (coeffOf (pmul (pmul (pneg gamma) h11) cP) t +
                coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h11)) t)) := by
          rw [coeffOf_append, coeff_dist4]
    _ = ((coeffOf (pmul cP cP) t + coeffOf (pmul cP (pmul gamma h11)) t) +
          (coeffOf (pmul (pmul (pneg gamma) h11) cP) t +
            coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h11)) t)) +
          coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h01)) t := by
          rw [Gauss.add_comm]
    _ = ((coeffOf (pmul cP cP) t +
          coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h11)) t) +
          (coeffOf (pmul cP (pmul gamma h11)) t +
            coeffOf (pmul (pmul (pneg gamma) h11) cP) t)) +
          coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h01)) t := by
          rw [Gauss.add_comm
              (coeffOf (pmul (pmul (pneg gamma) h11) cP) t)
              (coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h11)) t),
            Gauss.add_add_add_comm]
    _ = (coeffOf (pmul cP cP) t +
          coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h11)) t) +
          coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h01)) t := by
          rw [coeff_slide_cancel cP gamma h11, Gauss.add_zero]
    _ = coeffOf (pmul cP cP) t + coeffOf (pmul (single 1 sSq) axisSq) t := by
          rw [Gauss.add_assoc, coeff_axis_scaled_11]
    _ = coeffOf (pmul cP cP ++ pmul (single 1 sSq) axisSq) t := by
          rw [← coeffOf_append]

theorem evolution_off_01 (t : Mono) :
    coeffOf (matMul (matDagger evolution) evolution).a01 t = 0 := by
  rw [evolution_dagger, evolution]
  have hentry :
      (matMul (lin cP (pneg gamma) hamiltonian) (lin cP gamma hamiltonian)).a01 =
        pmul (cP ++ pmul (pneg gamma) h00) (pmul gamma h01) ++
          pmul (pmul (pneg gamma) h01) (cP ++ pmul gamma h11) := by
    unfold matMul lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  rw [hentry]
  calc
    coeffOf (pmul (cP ++ pmul (pneg gamma) h00) (pmul gamma h01) ++
        pmul (pmul (pneg gamma) h01) (cP ++ pmul gamma h11)) t
        = (coeffOf (pmul cP (pmul gamma h01)) t +
            coeffOf (pmul (pmul (pneg gamma) h00) (pmul gamma h01)) t) +
            (coeffOf (pmul (pmul (pneg gamma) h01) cP) t +
              coeffOf (pmul (pmul (pneg gamma) h01) (pmul gamma h11)) t) := by
          rw [coeffOf_append, pmul_append_left, coeffOf_append, coeff_mul_append_right,
            coeffOf_append]
    _ = (coeffOf (pmul cP (pmul gamma h01)) t +
          coeffOf (pmul (pmul (pneg gamma) h01) cP) t) +
          (coeffOf (pmul (pmul (pneg gamma) h00) (pmul gamma h01)) t +
            coeffOf (pmul (pmul (pneg gamma) h01) (pmul gamma h11)) t) :=
          Gauss.add_add_add_comm _ _ _ _
    _ = 0 := by rw [coeff_slide_cancel cP gamma h01, Gauss.zero_add, coeff_off_scaled]

theorem evolution_off_10 (t : Mono) :
    coeffOf (matMul (matDagger evolution) evolution).a10 t = 0 := by
  rw [evolution_dagger, evolution]
  have hentry :
      (matMul (lin cP (pneg gamma) hamiltonian) (lin cP gamma hamiltonian)).a10 =
        pmul (pmul (pneg gamma) h10) (cP ++ pmul gamma h00) ++
          pmul (cP ++ pmul (pneg gamma) h11) (pmul gamma h10) := by
    unfold matMul lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  rw [hentry]
  calc
    coeffOf (pmul (pmul (pneg gamma) h10) (cP ++ pmul gamma h00) ++
        pmul (cP ++ pmul (pneg gamma) h11) (pmul gamma h10)) t
        = (coeffOf (pmul (pmul (pneg gamma) h10) cP) t +
            coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h00)) t) +
            (coeffOf (pmul cP (pmul gamma h10)) t +
              coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h10)) t) := by
          rw [coeffOf_append, coeff_mul_append_right, pmul_append_left, coeffOf_append,
            coeffOf_append]
    _ = (coeffOf (pmul cP (pmul gamma h10)) t +
          coeffOf (pmul (pmul (pneg gamma) h10) cP) t) +
          (coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h10)) t +
            coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h00)) t) := by
          rw [Gauss.add_comm
              (coeffOf (pmul (pmul (pneg gamma) h10) cP) t +
                coeffOf (pmul (pmul (pneg gamma) h10) (pmul gamma h00)) t)
              (coeffOf (pmul cP (pmul gamma h10)) t +
                coeffOf (pmul (pmul (pneg gamma) h11) (pmul gamma h10)) t),
            Gauss.add_add_add_comm]
    _ = 0 := by rw [coeff_slide_cancel cP gamma h10, Gauss.zero_add, coeff_off_scaled_10]

theorem coeff_c_sq (t : Mono) : coeffOf (pmul cP cP) t = if cSq = t then 1 else 0 := by
  rw [cP, coeff_single_mul, c1_sq, Gauss.mul_one]

theorem coeff_s_neg (t : Mono) :
    coeffOf (pmul (single (1 : Gauss) sSq) (single (-1) Mono.one)) t =
      if sSq = t then -1 else 0 := by
  rw [coeff_single_mul, Mono.mul_one, Gauss.mul_neg, Gauss.mul_one]

theorem s_cancel (t : Mono) :
    (if sSq = t then (1 : Gauss) else 0) + (if sSq = t then -1 else 0) = 0 := by
  by_cases h : sSq = t
  · rw [ite_eq_left h, ite_eq_left h, Gauss.add_neg_cancel]
  · rw [ite_eq_right h, ite_eq_right h, Gauss.zero_add]

theorem gauss_defect_reassoc (a s p m n : Gauss) (h : p + m = 0) :
    (a + s) + n = (a + p) + n + (s + m) := by
  refine Eq.symm ?_
  calc
    (a + p) + n + (s + m) = (a + p) + (n + (s + m)) := Gauss.add_assoc _ _ _
    _ = (a + p) + ((n + s) + m) := by rw [← Gauss.add_assoc n s m]
    _ = (a + p) + ((s + n) + m) := by rw [Gauss.add_comm n s]
    _ = (a + p) + (s + (n + m)) := by rw [Gauss.add_assoc s n m]
    _ = (a + p) + (s + (m + n)) := by rw [Gauss.add_comm n m]
    _ = (a + p) + ((s + m) + n) := by rw [← Gauss.add_assoc s m n]
    _ = (a + p) + (s + m) + n := by rw [← Gauss.add_assoc (a + p) (s + m) n]
    _ = (a + s) + (p + m) + n := by rw [Gauss.add_add_add_comm a p s m]
    _ = (a + s) + 0 + n := by rw [h]
    _ = (a + s) + n := by rw [Gauss.add_zero (a + s)]

theorem scalar_defect (t : Mono) :
    coeffOf (psub scalarμ (single 1 Mono.one)) t = coeffOf unitaryDefect t := by
  have hconst : -(if Mono.one = t then (1 : Gauss) else 0) =
      coeffOf (single (-1) Mono.one) t := by
    rw [coeff_single_eq]
    by_cases h : Mono.one = t
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, Gauss.neg_zero]
  rw [coeff_psub, scalarμ, coeffOf_append, coeff_single_eq, coeff_c_sq, unitaryDefect]
  rw [show gN = axisSq ++ single (-1) Mono.one from axis_tail.symm]
  rw [coeffOf_append, coeff_mul_append_right, coeffOf_append, coeff_s_neg, gC]
  rw [coeffOf_append, coeffOf_append, coeff_single_eq, coeff_single_eq, hconst]
  exact gauss_defect_reassoc
    (if cSq = t then 1 else 0)
    (coeffOf (pmul (single 1 sSq) axisSq) t)
    (if sSq = t then 1 else 0)
    (if sSq = t then -1 else 0)
    (coeffOf (single (-1) Mono.one) t)
    (s_cancel t)

theorem evolution_unitary_00 :
    polySame (psub (matMul (matDagger evolution) evolution).a00 (single 1 Mono.one))
      unitaryDefect :=
  fun t => (by rw [coeff_psub, evolution_diag_00, ← coeff_psub, scalar_defect])

theorem evolution_unitary_11 :
    polySame (psub (matMul (matDagger evolution) evolution).a11 (single 1 Mono.one))
      unitaryDefect :=
  fun t => (by rw [coeff_psub, evolution_diag_11, ← coeff_psub, scalar_defect])

theorem evolution_unitary_01 : polySame (matMul (matDagger evolution) evolution).a01 [] := by
  intro t
  rw [evolution_off_01, coeffOf_nil]

theorem evolution_unitary_10 : polySame (matMul (matDagger evolution) evolution).a10 [] := by
  intro t
  rw [evolution_off_10, coeffOf_nil]

theorem unitary_ideal : inIdeal unitaryDefect :=
  inIdeal_append inIdeal_gC (inIdeal_mul_left (single 1 sSq) inIdeal_gN)

/-- `U†U − I` ha cofattori `1 · gC + s² · gN` sulla diagonale. -/
theorem evolution_unitary : matRel (matMul (matDagger evolution) evolution) matOne :=
  ⟨inIdeal_polySame evolution_unitary_00 unitary_ideal, ideal_of_zero _ evolution_unitary_01,
    ideal_of_zero _ evolution_unitary_10, inIdeal_polySame evolution_unitary_11 unitary_ideal⟩

/-! ### `UU†` -/

theorem coeff_slide_cancel_rev (p q a : Poly) (t : Mono) :
    coeffOf (pmul p (pmul (pneg q) a)) t + coeffOf (pmul (pmul q a) p) t = 0 := by
  have hleft : polySame (pmul p (pneg q)) (pneg (pmul p q)) := by
    intro u
    rw [coeff_pmul_pneg_right, coeff_pneg]
  calc
    coeffOf (pmul p (pmul (pneg q) a)) t + coeffOf (pmul (pmul q a) p) t
        = coeffOf (pmul p (pmul (pneg q) a)) t + coeffOf (pmul p (pmul q a)) t := by
          rw [coeff_mul_comm (pmul q a) p]
    _ = coeffOf (pmul (pmul p (pneg q)) a) t + coeffOf (pmul (pmul p q) a) t := by
          rw [← pmul_assoc p (pneg q) a, ← pmul_assoc p q a]
    _ = coeffOf (pmul (pneg (pmul p q)) a) t + coeffOf (pmul (pmul p q) a) t := by
          rw [coeff_mul_congr_left hleft]
    _ = -coeffOf (pmul (pmul p q) a) t + coeffOf (pmul (pmul p q) a) t := by
          rw [← pneg_pmul, coeff_pneg]
    _ = 0 := by rw [Gauss.add_comm, Gauss.add_neg_cancel]

theorem gamma_factor_swap (t : Mono) :
    coeffOf (pmul gamma (pneg gamma)) t = coeffOf (single 1 sSq) t := by
  rw [coeff_mul_comm, gamma_factor]

theorem coeff_axis_scaled_rev (t : Mono) :
    coeffOf (pmul (pmul gamma h00) (pmul (pneg gamma) h00)) t +
        coeffOf (pmul (pmul gamma h01) (pmul (pneg gamma) h10)) t =
      coeffOf (pmul (single 1 sSq) axisSq) t := by
  have h0 := polySame_assoc_comm gamma h00 (pneg gamma) h00 t
  have h1 := polySame_assoc_comm gamma h01 (pneg gamma) h10 t
  rw [h0, h1, coeff_scale_sum]
  rw [show pmul h00 h00 ++ pmul h01 h10 = (matMul hamiltonian hamiltonian).a00 from rfl]
  rw [coeff_mul_congr_right diag_00, coeff_mul_congr_left gamma_factor_swap]

theorem coeff_axis_scaled_11_rev (t : Mono) :
    coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h11)) t +
        coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h01)) t =
      coeffOf (pmul (single 1 sSq) axisSq) t := by
  have h0 := polySame_assoc_comm gamma h11 (pneg gamma) h11 t
  have h1 := polySame_assoc_comm gamma h10 (pneg gamma) h01 t
  have hswap : polySame (pmul h11 h11 ++ pmul h10 h01) (pmul h10 h01 ++ pmul h11 h11) := by
    intro u
    rw [coeffOf_append, coeffOf_append, Gauss.add_comm]
  rw [h0, h1, coeff_scale_sum, coeff_mul_congr_right hswap]
  rw [show pmul h10 h01 ++ pmul h11 h11 = (matMul hamiltonian hamiltonian).a11 from rfl]
  rw [coeff_mul_congr_right diag_11, coeff_mul_congr_left gamma_factor_swap]

theorem coeff_off_scaled_rev (t : Mono) :
    coeffOf (pmul (pmul gamma h00) (pmul (pneg gamma) h01)) t +
        coeffOf (pmul (pmul gamma h01) (pmul (pneg gamma) h11)) t = 0 := by
  have h0 := polySame_assoc_comm gamma h00 (pneg gamma) h01 t
  have h1 := polySame_assoc_comm gamma h01 (pneg gamma) h11 t
  rw [h0, h1, coeff_scale_sum]
  rw [show pmul h00 h01 ++ pmul h01 h11 = (matMul hamiltonian hamiltonian).a01 from rfl]
  rw [coeff_mul_congr_right off_01, pmul_nil, coeffOf_nil]

theorem coeff_off_scaled_10_rev (t : Mono) :
    coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h10)) t +
        coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h00)) t = 0 := by
  have h0 := polySame_assoc_comm gamma h11 (pneg gamma) h10 t
  have h1 := polySame_assoc_comm gamma h10 (pneg gamma) h00 t
  have hswap : polySame (pmul h11 h10 ++ pmul h10 h00) (pmul h10 h00 ++ pmul h11 h10) := by
    intro u
    rw [coeffOf_append, coeffOf_append, Gauss.add_comm]
  rw [h0, h1, coeff_scale_sum, coeff_mul_congr_right hswap]
  rw [show pmul h10 h00 ++ pmul h11 h10 = (matMul hamiltonian hamiltonian).a10 from rfl]
  rw [coeff_mul_congr_right off_10, pmul_nil, coeffOf_nil]

theorem evolution_rev_diag_00 (t : Mono) :
    coeffOf (matMul evolution (matDagger evolution)).a00 t = coeffOf scalarμ t := by
  rw [evolution_dagger, evolution]
  have hentry :
      (matMul (lin cP gamma hamiltonian) (lin cP (pneg gamma) hamiltonian)).a00 =
        pmul (cP ++ pmul gamma h00) (cP ++ pmul (pneg gamma) h00) ++
          pmul (pmul gamma h01) (pmul (pneg gamma) h10) := by
    unfold matMul lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  rw [hentry, scalarμ]
  calc
    coeffOf (pmul (cP ++ pmul gamma h00) (cP ++ pmul (pneg gamma) h00) ++
        pmul (pmul gamma h01) (pmul (pneg gamma) h10)) t
        = ((coeffOf (pmul cP cP) t + coeffOf (pmul cP (pmul (pneg gamma) h00)) t) +
            (coeffOf (pmul (pmul gamma h00) cP) t +
              coeffOf (pmul (pmul gamma h00) (pmul (pneg gamma) h00)) t)) +
            coeffOf (pmul (pmul gamma h01) (pmul (pneg gamma) h10)) t := by
          rw [coeffOf_append, coeff_dist4]
    _ = ((coeffOf (pmul cP cP) t +
          coeffOf (pmul (pmul gamma h00) (pmul (pneg gamma) h00)) t) +
          (coeffOf (pmul cP (pmul (pneg gamma) h00)) t +
            coeffOf (pmul (pmul gamma h00) cP) t)) +
          coeffOf (pmul (pmul gamma h01) (pmul (pneg gamma) h10)) t := by
          rw [Gauss.add_comm
              (coeffOf (pmul (pmul gamma h00) cP) t)
              (coeffOf (pmul (pmul gamma h00) (pmul (pneg gamma) h00)) t),
            Gauss.add_add_add_comm]
    _ = (coeffOf (pmul cP cP) t +
          coeffOf (pmul (pmul gamma h00) (pmul (pneg gamma) h00)) t) +
          coeffOf (pmul (pmul gamma h01) (pmul (pneg gamma) h10)) t := by
          rw [coeff_slide_cancel_rev cP gamma h00, Gauss.add_zero]
    _ = coeffOf (pmul cP cP) t + coeffOf (pmul (single 1 sSq) axisSq) t := by
          rw [Gauss.add_assoc, coeff_axis_scaled_rev]
    _ = coeffOf (pmul cP cP ++ pmul (single 1 sSq) axisSq) t := by
          rw [← coeffOf_append]

theorem evolution_rev_diag_11 (t : Mono) :
    coeffOf (matMul evolution (matDagger evolution)).a11 t = coeffOf scalarμ t := by
  rw [evolution_dagger, evolution]
  have hentry :
      (matMul (lin cP gamma hamiltonian) (lin cP (pneg gamma) hamiltonian)).a11 =
        pmul (pmul gamma h10) (pmul (pneg gamma) h01) ++
          pmul (cP ++ pmul gamma h11) (cP ++ pmul (pneg gamma) h11) := by
    unfold matMul lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  rw [hentry, scalarμ]
  calc
    coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h01) ++
        pmul (cP ++ pmul gamma h11) (cP ++ pmul (pneg gamma) h11)) t
        = coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h01)) t +
            ((coeffOf (pmul cP cP) t + coeffOf (pmul cP (pmul (pneg gamma) h11)) t) +
              (coeffOf (pmul (pmul gamma h11) cP) t +
                coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h11)) t)) := by
          rw [coeffOf_append, coeff_dist4]
    _ = ((coeffOf (pmul cP cP) t + coeffOf (pmul cP (pmul (pneg gamma) h11)) t) +
          (coeffOf (pmul (pmul gamma h11) cP) t +
            coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h11)) t)) +
          coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h01)) t := by
          rw [Gauss.add_comm]
    _ = ((coeffOf (pmul cP cP) t +
          coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h11)) t) +
          (coeffOf (pmul cP (pmul (pneg gamma) h11)) t +
            coeffOf (pmul (pmul gamma h11) cP) t)) +
          coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h01)) t := by
          rw [Gauss.add_comm
              (coeffOf (pmul (pmul gamma h11) cP) t)
              (coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h11)) t),
            Gauss.add_add_add_comm]
    _ = (coeffOf (pmul cP cP) t +
          coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h11)) t) +
          coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h01)) t := by
          rw [coeff_slide_cancel_rev cP gamma h11, Gauss.add_zero]
    _ = coeffOf (pmul cP cP) t + coeffOf (pmul (single 1 sSq) axisSq) t := by
          rw [Gauss.add_assoc, coeff_axis_scaled_11_rev]
    _ = coeffOf (pmul cP cP ++ pmul (single 1 sSq) axisSq) t := by
          rw [← coeffOf_append]

theorem evolution_rev_off_01 (t : Mono) :
    coeffOf (matMul evolution (matDagger evolution)).a01 t = 0 := by
  rw [evolution_dagger, evolution]
  have hentry :
      (matMul (lin cP gamma hamiltonian) (lin cP (pneg gamma) hamiltonian)).a01 =
        pmul (cP ++ pmul gamma h00) (pmul (pneg gamma) h01) ++
          pmul (pmul gamma h01) (cP ++ pmul (pneg gamma) h11) := by
    unfold matMul lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  rw [hentry]
  calc
    coeffOf (pmul (cP ++ pmul gamma h00) (pmul (pneg gamma) h01) ++
        pmul (pmul gamma h01) (cP ++ pmul (pneg gamma) h11)) t
        = (coeffOf (pmul cP (pmul (pneg gamma) h01)) t +
            coeffOf (pmul (pmul gamma h00) (pmul (pneg gamma) h01)) t) +
            (coeffOf (pmul (pmul gamma h01) cP) t +
              coeffOf (pmul (pmul gamma h01) (pmul (pneg gamma) h11)) t) := by
          rw [coeffOf_append, pmul_append_left, coeffOf_append, coeff_mul_append_right,
            coeffOf_append]
    _ = (coeffOf (pmul cP (pmul (pneg gamma) h01)) t +
          coeffOf (pmul (pmul gamma h01) cP) t) +
          (coeffOf (pmul (pmul gamma h00) (pmul (pneg gamma) h01)) t +
            coeffOf (pmul (pmul gamma h01) (pmul (pneg gamma) h11)) t) :=
          Gauss.add_add_add_comm _ _ _ _
    _ = 0 := by rw [coeff_slide_cancel_rev cP gamma h01, Gauss.zero_add, coeff_off_scaled_rev]

theorem evolution_rev_off_10 (t : Mono) :
    coeffOf (matMul evolution (matDagger evolution)).a10 t = 0 := by
  rw [evolution_dagger, evolution]
  have hentry :
      (matMul (lin cP gamma hamiltonian) (lin cP (pneg gamma) hamiltonian)).a10 =
        pmul (pmul gamma h10) (cP ++ pmul (pneg gamma) h00) ++
          pmul (cP ++ pmul gamma h11) (pmul (pneg gamma) h10) := by
    unfold matMul lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  rw [hentry]
  calc
    coeffOf (pmul (pmul gamma h10) (cP ++ pmul (pneg gamma) h00) ++
        pmul (cP ++ pmul gamma h11) (pmul (pneg gamma) h10)) t
        = (coeffOf (pmul (pmul gamma h10) cP) t +
            coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h00)) t) +
            (coeffOf (pmul cP (pmul (pneg gamma) h10)) t +
              coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h10)) t) := by
          rw [coeffOf_append, coeff_mul_append_right, pmul_append_left, coeffOf_append,
            coeffOf_append]
    _ = (coeffOf (pmul cP (pmul (pneg gamma) h10)) t +
          coeffOf (pmul (pmul gamma h10) cP) t) +
          (coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h10)) t +
            coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h00)) t) := by
          rw [Gauss.add_comm
              (coeffOf (pmul (pmul gamma h10) cP) t +
                coeffOf (pmul (pmul gamma h10) (pmul (pneg gamma) h00)) t)
              (coeffOf (pmul cP (pmul (pneg gamma) h10)) t +
                coeffOf (pmul (pmul gamma h11) (pmul (pneg gamma) h10)) t),
            Gauss.add_add_add_comm]
    _ = 0 := by
          rw [coeff_slide_cancel_rev cP gamma h10, Gauss.zero_add, coeff_off_scaled_10_rev]

theorem evolution_rev_00 :
    polySame (psub (matMul evolution (matDagger evolution)).a00 (single 1 Mono.one))
      unitaryDefect :=
  fun t => (by rw [coeff_psub, evolution_rev_diag_00, ← coeff_psub, scalar_defect])

theorem evolution_rev_11 :
    polySame (psub (matMul evolution (matDagger evolution)).a11 (single 1 Mono.one))
      unitaryDefect :=
  fun t => (by rw [coeff_psub, evolution_rev_diag_11, ← coeff_psub, scalar_defect])

theorem evolution_rev_01 : polySame (matMul evolution (matDagger evolution)).a01 [] := by
  intro t
  rw [evolution_rev_off_01, coeffOf_nil]

theorem evolution_rev_10 : polySame (matMul evolution (matDagger evolution)).a10 [] := by
  intro t
  rw [evolution_rev_off_10, coeffOf_nil]

/-- `UU† − I` ha gli stessi cofattori `1 · gC + s² · gN`. -/
theorem evolution_unitary_rev : matRel (matMul evolution (matDagger evolution)) matOne :=
  ⟨inIdeal_polySame evolution_rev_00 unitary_ideal, ideal_of_zero _ evolution_rev_01,
    ideal_of_zero _ evolution_rev_10, inIdeal_polySame evolution_rev_11 unitary_ideal⟩

/-! ### Determinante -/

def detEntry (M : Mat) : Poly := psub (pmul M.a00 M.a11) (pmul M.a01 M.a10)

theorem gamma_sq (t : Mono) :
    coeffOf (pmul gamma gamma) t = coeffOf (single (-1) sSq) t := by
  rw [gamma, coeff_single_mul, s1_sq, minus_i_sq, coeff_single_eq]

theorem coeff_single_neg_left (a : Gauss) (m : Mono) (p : Poly) (t : Mono) :
    coeffOf (pmul (single (-a) m) p) t = -coeffOf (pmul (single a m) p) t := by
  rw [show single (-a) m = pneg (single a m) from rfl, ← pneg_pmul, coeff_pneg]

theorem det_hamiltonian (t : Mono) :
    coeffOf (psub (pmul h00 h11) (pmul h01 h10)) t = coeffOf (pneg axisSq) t := by
  rw [coeff_psub, h11_neg, coeff_pmul_pneg_right, coeff_nz_sq, coeff_h01_h10, coeff_pneg, axisSq,
    coeffOf_append (single 1 nxSq ++ single 1 nySq) (single 1 nzSq), Gauss.neg_add]
  exact Gauss.add_comm _ _

theorem evolution_det_coeff (t : Mono) :
    coeffOf (detEntry evolution) t = coeffOf scalarμ t := by
  have ha00 : evolution.a00 = cP ++ pmul gamma h00 := by
    unfold evolution lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  have ha11 : evolution.a11 = cP ++ pmul gamma h11 := by
    unfold evolution lin hamiltonian
    dsimp only [pmul, Universe.Quotient.mul, mulMono, single, cP, Mono.mul, Mono.one]
    rw [Gauss.mul_one, List.append_nil]
    rfl
  have ha01 : evolution.a01 = pmul gamma h01 := rfl
  have ha10 : evolution.a10 = pmul gamma h10 := rfl
  rw [detEntry, ha00, ha11, ha01, ha10]
  have hcross : coeffOf (pmul cP (pmul gamma h11)) t + coeffOf (pmul (pmul gamma h00) cP) t = 0 := by
    rw [h11_neg, ← pmul_assoc, coeff_pmul_pneg_right, pmul_assoc, coeff_mul_comm, Gauss.add_comm,
      Gauss.add_neg_cancel]
  have htail : coeffOf (pmul (pmul gamma h00) (pmul gamma h11)) t +
      -coeffOf (pmul (pmul gamma h01) (pmul gamma h10)) t =
      coeffOf (pmul (single 1 sSq) axisSq) t := by
    have h0 := polySame_assoc_comm gamma h00 gamma h11 t
    have h1 := polySame_assoc_comm gamma h01 gamma h10 t
    rw [h0, h1, ← coeff_psub,
      (polySame.symm (polySame_mul_psub_right (pmul gamma gamma) (pmul h00 h11) (pmul h01 h10))) t,
      coeff_mul_congr_right det_hamiltonian, coeff_pmul_pneg_right, coeff_mul_congr_left gamma_sq,
      coeff_single_neg_left, Gauss.neg_neg]
  rw [scalarμ, coeff_psub, coeffOf_append, coeff_dist4, Gauss.add_comm
      (coeffOf (pmul (pmul gamma h00) cP) t)
      (coeffOf (pmul (pmul gamma h00) (pmul gamma h11)) t),
    Gauss.add_add_add_comm, hcross, Gauss.add_zero, Gauss.add_assoc, htail, ← coeffOf_append]

/-- `det U − 1` ha cofattori `1 · gC + s² · gN`. -/
theorem evolution_det : inIdeal (psub (detEntry evolution) (single 1 Mono.one)) := by
  have h : polySame (psub (detEntry evolution) (single 1 Mono.one)) unitaryDefect := by
    intro t
    rw [coeff_psub, evolution_det_coeff, ← coeff_psub, scalar_defect]
  exact inIdeal_polySame h unitary_ideal

/-! ### Norma, per ampiezze arbitrarie -/

def normAmp (α β : Poly) : Poly := pmul (conjP α) α ++ pmul (conjP β) β

/-- `ψ† M ψ`. -/
def sandwich (M : Mat) (α β : Poly) : Poly :=
  pmul (conjP α) (pmul M.a00 α ++ pmul M.a01 β) ++
    pmul (conjP β) (pmul M.a10 α ++ pmul M.a11 β)

theorem polySame_append_nil (p : Poly) : polySame (p ++ []) p := by
  intro t
  rw [List.append_nil]

theorem polySame_nil_append (p : Poly) : polySame ([] ++ p) p := by
  intro t
  rw [List.nil_append]

theorem polySame_mul_nil_right (p β : Poly) (h : polySame p []) : polySame (pmul p β) [] := by
  intro t
  rw [coeff_mul_congr_left h, show pmul [] β = [] from rfl, coeffOf_nil]

theorem polySame_scalar_move (μ p : Poly) :
    polySame (pmul (conjP p) (pmul μ p)) (pmul μ (pmul (conjP p) p)) := by
  intro t
  calc
    coeffOf (pmul (conjP p) (pmul μ p)) t
        = coeffOf (pmul (pmul (conjP p) μ) p) t := by rw [← pmul_assoc (conjP p) μ p]
    _ = coeffOf (pmul (pmul μ (conjP p)) p) t := by
          rw [coeff_mul_congr_left (coeff_mul_comm (conjP p) μ)]
    _ = coeffOf (pmul μ (pmul (conjP p) p)) t := by rw [pmul_assoc μ (conjP p) p]

theorem sandwich_scalar (μ : Poly) (M : Mat) (α β : Poly) (h00 : polySame M.a00 μ)
    (h11 : polySame M.a11 μ) (h01 : polySame M.a01 []) (h10 : polySame M.a10 []) :
    polySame (sandwich M α β) (pmul μ (normAmp α β)) := by
  have row0 : polySame (pmul M.a00 α ++ pmul M.a01 β) (pmul μ α) :=
    polySame.trans (polySame_append (polySame_pmul_left h00 α) (polySame_mul_nil_right _ _ h01))
      (polySame_append_nil _)
  have row1 : polySame (pmul M.a10 α ++ pmul M.a11 β) (pmul μ β) :=
    polySame.trans (polySame_append (polySame_mul_nil_right _ _ h10) (polySame_pmul_left h11 β))
      (polySame_nil_append _)
  have left : polySame (pmul (conjP α) (pmul M.a00 α ++ pmul M.a01 β))
      (pmul μ (pmul (conjP α) α)) :=
    polySame.trans (polySame_pmul_right row0 (conjP α)) (polySame_scalar_move μ α)
  have right : polySame (pmul (conjP β) (pmul M.a10 α ++ pmul M.a11 β))
      (pmul μ (pmul (conjP β) β)) :=
    polySame.trans (polySame_pmul_right row1 (conjP β)) (polySame_scalar_move μ β)
  intro t
  rw [sandwich, normAmp, coeffOf_append, left t, right t, ← coeffOf_append, ← coeff_mul_append_right]

/-- `ψ† (U†U) ψ − ‖ψ‖²` sta nell'ideale, per ogni ampiezza `α, β`. -/
theorem evolution_norm (α β : Poly) :
    inIdeal (psub (sandwich (matMul (matDagger evolution) evolution) α β) (normAmp α β)) := by
  have hsand := sandwich_scalar scalarμ (matMul (matDagger evolution) evolution) α β
    evolution_diag_00 evolution_diag_11 evolution_unitary_01 evolution_unitary_10
  have hdiff : polySame
      (psub (sandwich (matMul (matDagger evolution) evolution) α β) (normAmp α β))
      (pmul (psub scalarμ (single 1 Mono.one)) (normAmp α β)) := by
    intro t
    have hsub : coeffOf (normAmp α β) t =
        coeffOf (pmul (single 1 Mono.one) (normAmp α β)) t := by rw [one_pmul]
    rw [coeff_psub, hsub, hsand t, ← coeff_psub,
      (polySame.symm (polySame_mul_psub_left scalarμ (single 1 Mono.one) (normAmp α β))) t]
  exact inIdeal_polySame hdiff
    (inIdeal_mul_right (normAmp α β) (inIdeal_polySame scalar_defect unitary_ideal))

end Universe.Qubit
