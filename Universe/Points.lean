/-
Tabella dei punti razionali.

Ogni voce è il membro sinistro del teorema che la dimostra.
Un `example` la lega al valore dimostrato: il numero stampato e il
numero dimostrato sono lo stesso termine. `lake exe points` stampa
`chiave re im`.
-/
import Universe.Angle
import Universe.Epistemology
import Universe.Interaction
import Universe.Symmetry

namespace Universe.Points

open Universe.Ring
open Universe.Epistemology
open Universe.Qubit
open Universe.Composition
open Universe.Dynamics
open Universe.Evaluation
open Universe.Observer
open Universe.Interaction
open Universe.Symmetry
open Universe.Angle

/-- P(0) nel punto. `Universe.Epistemology.point_prob0`. -/
def p0 : Gauss :=
  evalAt pointC pointS 1 0 0 (columnBorn (specPoly keepX evolution.a00))

example : p0 = ⟨(9 : Rat) / 25, 0⟩ := point_prob0

/-- P(1) nel punto. `Universe.Epistemology.point_prob1`. -/
def p1 : Gauss :=
  evalAt pointC pointS 1 0 0 (columnBorn (specPoly keepX evolution.a10))

example : p1 = ⟨(16 : Rat) / 25, 0⟩ := point_prob1

/-- `U₀₀` nel punto. `Universe.Symmetry.point_u_row0`. -/
def u00 : Gauss :=
  evalAt2 pointC pointS 1 0 0 pointC pointS evolution.a00

example : u00 = basisReal := point_u_row0.1

/-- `U₀₁` nel punto. `Universe.Symmetry.point_u_row0`. -/
def u01 : Gauss :=
  evalAt2 pointC pointS 1 0 0 pointC pointS evolution.a01

example : u01 = basisImag := point_u_row0.2

/-- `U₁₀` nel punto. `Universe.Symmetry.point_u_row1`. -/
def u10 : Gauss :=
  evalAt2 pointC pointS 1 0 0 pointC pointS evolution.a10

example : u10 = basisImag := point_u_row1.1

/-- `U₁₁` nel punto. `Universe.Symmetry.point_u_row1`. -/
def u11 : Gauss :=
  evalAt2 pointC pointS 1 0 0 pointC pointS evolution.a11

example : u11 = basisReal := point_u_row1.2

/-- Cella `|00⟩` di Bell. `Universe.Observer.point_bell`. -/
def bell00 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (applyCNOT (tensorPair (applyMat evolution ket0) ket0)).a0)

example : bell00 = pointAlpha := point_bell.1

/-- Cella `|01⟩` di Bell. `Universe.Observer.point_bell`. -/
def bell01 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (applyCNOT (tensorPair (applyMat evolution ket0) ket0)).a1)

example : bell01 = 0 := point_bell.2.1

/-- Cella `|10⟩` di Bell. `Universe.Observer.point_bell`. -/
def bell10 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (applyCNOT (tensorPair (applyMat evolution ket0) ket0)).a2)

example : bell10 = 0 := point_bell.2.2.1

/-- Cella `|11⟩` di Bell. `Universe.Observer.point_bell`. -/
def bell11 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (applyCNOT (tensorPair (applyMat evolution ket0) ket0)).a3)

example : bell11 = pointBeta := point_bell.2.2.2

/-- Determinante di Bell. `Universe.Observer.point_entangled`. -/
def bellDet : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (quadDet (applyCNOT (tensorPair (applyMat evolution ket0) ket0))))

example : bellDet = ⟨0, -((12 : Rat) / 25)⟩ := point_entangled

/-- Purezza dopo `CNOT`. `Universe.Observer.point_purity`. -/
def purityAt : Gauss :=
  evalAt pointC pointS 1 0 0
    (purity (reduceLeft (applyCNOT (tensorPair (applyMat evolution ket0) ket0))))

example : purityAt = ⟨(337 : Rat) / 625, 0⟩ := point_purity.1

/-- Coerenza, amico disfatto. `Universe.Observer.point_undone`. -/
def undoneCoh : Gauss :=
  evalAt pointC pointS 1 0 0
    (reduceSystem (cnot01 (cnot01
      (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0)))).a01

example : undoneCoh = ⟨0, (12 : Rat) / 25⟩ := point_undone.1

/-- Purezza, amico disfatto. `Universe.Observer.point_undone`. -/
def undonePur : Gauss :=
  evalAt pointC pointS 1 0 0
    (purity (reduceSystem (cnot01 (cnot01
      (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0)))))

example : undonePur = ⟨1, 0⟩ := point_undone.2

/-- Coerenza dopo la copia. `Universe.Observer.point_copied`. -/
def copiedCoh : Gauss :=
  evalAt pointC pointS 1 0 0
    (reduceSystem (cnot01 (cnot12 (cnot01
      (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0))))).a01

example : copiedCoh = 0 := point_copied.1

/-- Purezza dopo la copia. `Universe.Observer.point_copied`. -/
def copiedPur : Gauss :=
  evalAt pointC pointS 1 0 0
    (purity (reduceSystem (cnot01 (cnot12 (cnot01
      (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0))))))

example : copiedPur = ⟨(337 : Rat) / 625, 0⟩ := point_copied.2.1

/-- Peso `0` di Wigner dopo la copia. `Universe.Observer.point_copied`. -/
def copiedW0 : Gauss :=
  evalAt pointC pointS 1 0 0
    (marginalWigner (cnot01 (cnot12 (cnot01
      (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0))))).a0

example : copiedW0 = ⟨(9 : Rat) / 25, 0⟩ := point_copied.2.2.1

/-- Peso `1` di Wigner dopo la copia. `Universe.Observer.point_copied`. -/
def copiedW1 : Gauss :=
  evalAt pointC pointS 1 0 0
    (marginalWigner (cnot01 (cnot12 (cnot01
      (tensorLeft (tensorPair (applyMat evolution ket0) ket0) ket0))))).a1

example : copiedW1 = ⟨(16 : Rat) / 25, 0⟩ := point_copied.2.2.2

/-- Coerenza, coupling `(1, 0)`. `Universe.Interaction.point_partial_idle`. -/
def idleCoh : Gauss :=
  evalAt 1 0 1 0 0 (reduceLeft (partialState probePair)).a01

example : idleCoh = ⟨0, (12 : Rat) / 25⟩ := point_partial_idle.1

/-- Purezza, coupling `(1, 0)`. `Universe.Interaction.point_partial_idle`. -/
def idlePur : Gauss :=
  evalAt 1 0 1 0 0 (purity (reduceLeft (partialState probePair)))

example : idlePur = ⟨1, 0⟩ := point_partial_idle.2

/-- Coerenza, coupling `(3/5, 4/5)`. `Universe.Interaction.point_partial_mid`. -/
def midCoh : Gauss :=
  evalAt pointC pointS 1 0 0 (reduceLeft (partialState probePair)).a01

example : midCoh = ⟨0, (36 : Rat) / 125⟩ := point_partial_mid.1

/-- Purezza, coupling `(3/5, 4/5)`. `Universe.Interaction.point_partial_mid`. -/
def midPur : Gauss :=
  evalAt pointC pointS 1 0 0 (purity (reduceLeft (partialState probePair)))

example : midPur = ⟨(11017 : Rat) / 15625, 0⟩ := point_partial_mid.2

/-- Coerenza, coupling `(0, 1)`. `Universe.Interaction.point_partial_flip`. -/
def flipCoh : Gauss :=
  evalAt 0 1 1 0 0 (reduceLeft (partialState probePair)).a01

example : flipCoh = 0 := point_partial_flip.1

/-- Purezza, coupling `(0, 1)`. `Universe.Interaction.point_partial_flip`. -/
def flipPur : Gauss :=
  evalAt 0 1 1 0 0 (purity (reduceLeft (partialState probePair)))

example : flipPur = ⟨(337 : Rat) / 625, 0⟩ := point_partial_flip.2

/-- Lüders, lettura `0`, ampiezza `|0⟩`. `Universe.Interaction.point_luders`. -/
def luders00 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX
      (condition 0 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))).a0)

example : luders00 = pointAlpha := point_luders.1

/-- Lüders, lettura `0`, ampiezza `|1⟩`. `Universe.Interaction.point_luders`. -/
def luders01 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX
      (condition 0 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))).a1)

example : luders01 = 0 := point_luders.2.1

/-- Lüders, lettura `1`, ampiezza `|0⟩`. `Universe.Interaction.point_luders`. -/
def luders10 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX
      (condition 1 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))).a0)

example : luders10 = 0 := point_luders.2.2.1

/-- Lüders, lettura `1`, ampiezza `|1⟩`. `Universe.Interaction.point_luders`. -/
def luders11 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX
      (condition 1 (applyCNOT (tensorPair (applyMat evolution ket0) ket0))).a1)

example : luders11 = pointBeta := point_luders.2.2.2.1

/-- Norma della lettura `0`. `Universe.Interaction.point_luders`. -/
def ludersN0 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX
      (normPair (condition 0 (applyCNOT (tensorPair (applyMat evolution ket0) ket0)))))

example : ludersN0 = ⟨(9 : Rat) / 25, 0⟩ := point_luders.2.2.2.2.1

/-- Norma della lettura `1`. `Universe.Interaction.point_luders`. -/
def ludersN1 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX
      (normPair
        (condition 1 (applyCNOT (tensorPair (applyMat evolution ket0) ket0)))))

example : ludersN1 = ⟨(16 : Rat) / 25, 0⟩ := point_luders.2.2.2.2.2

/-- Seconda lettura `0`, esito `0`. `Universe.Interaction.point_repeatable`. -/
def repeat00 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (marginalRight (reread 0 (applyMat evolution ket0))).a0)

example : repeat00 = ⟨(9 : Rat) / 25, 0⟩ := point_repeatable.1

/-- Seconda lettura `0`, esito `1`. `Universe.Interaction.point_repeatable`. -/
def repeat01 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (marginalRight (reread 0 (applyMat evolution ket0))).a1)

example : repeat01 = 0 := point_repeatable.2.1

/-- Seconda lettura `1`, esito `0`. `Universe.Interaction.point_repeatable`. -/
def repeat10 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (marginalRight (reread 1 (applyMat evolution ket0))).a0)

example : repeat10 = 0 := point_repeatable.2.2.1

/-- Seconda lettura `1`, esito `1`. `Universe.Interaction.point_repeatable`. -/
def repeat11 : Gauss :=
  evalAt pointC pointS 1 0 0
    (specPoly keepX (marginalRight (reread 1 (applyMat evolution ket0))).a1)

example : repeat11 = ⟨(16 : Rat) / 25, 0⟩ := point_repeatable.2.2.2

/-- `V(U|0⟩)`, ampiezza `|0⟩`. `Universe.Symmetry.point_conj_evolution`. -/
def v0 : Gauss :=
  evalAt pointC pointS 1 0 0 (applyMat pointBasis (applyMat evolution ket0)).a0

example : v0 = ⟨-(7 : Rat) / 25, 0⟩ := point_conj_evolution.1

/-- `V(U|0⟩)`, ampiezza `|1⟩`. `Universe.Symmetry.point_conj_evolution`. -/
def v1 : Gauss :=
  evalAt pointC pointS 1 0 0 (applyMat pointBasis (applyMat evolution ket0)).a1

example : v1 = ⟨0, -(24 : Rat) / 25⟩ := point_conj_evolution.2.1

/-- `(V U V†)(V|0⟩)`, ampiezza `|0⟩`. `Universe.Symmetry.point_conj_evolution`. -/
def vConj0 : Gauss :=
  evalAt pointC pointS 1 0 0
    (applyMat (matMul (matMul pointBasis evolution) (matDagger pointBasis))
      (applyMat pointBasis ket0)).a0

example : vConj0 = ⟨-(7 : Rat) / 25, 0⟩ := point_conj_evolution.2.2.1

/-- `(V U V†)(V|0⟩)`, ampiezza `|1⟩`. `Universe.Symmetry.point_conj_evolution`. -/
def vConj1 : Gauss :=
  evalAt pointC pointS 1 0 0
    (applyMat (matMul (matMul pointBasis evolution) (matDagger pointBasis))
      (applyMat pointBasis ket0)).a1

example : vConj1 = ⟨0, -(24 : Rat) / 25⟩ := point_conj_evolution.2.2.2

/-- Peso di `V|0⟩` sulla base `V|0⟩`. `Universe.Symmetry.point_conj_born`. -/
def vW0 : Gauss :=
  evalAt pointC pointS 1 0 0
    (columnBorn (braket (matColumn pointBasis 0) (applyMat pointBasis ket0)))

example : vW0 = 1 := point_conj_born.1

/-- Peso di `V|0⟩` sulla base `V|1⟩`. `Universe.Symmetry.point_conj_born`. -/
def vW1 : Gauss :=
  evalAt pointC pointS 1 0 0
    (columnBorn (braket (matColumn pointBasis 1) (applyMat pointBasis ket0)))

example : vW1 = 0 := point_conj_born.2

/-- Angolo composto, coseno. `Universe.Symmetry.point_compose`. -/
def composeC : Gauss :=
  evalAt2 pointC pointS 1 0 0 pointC pointS angleC

example : composeC = ⟨-(7 : Rat) / 25, 0⟩ := point_compose.1

/-- Angolo composto, seno. `Universe.Symmetry.point_compose`. -/
def composeS : Gauss :=
  evalAt2 pointC pointS 1 0 0 pointC pointS angleS

example : composeS = ⟨(24 : Rat) / 25, 0⟩ := point_compose.2.1

/-- `U U₂|0⟩`, ampiezza `|0⟩`. `Universe.Symmetry.point_compose`. -/
def compose0 : Gauss :=
  evalAt2 pointC pointS 1 0 0 pointC pointS
    (applyMat (matMul evolution evolution2) ket0).a0

example : compose0 = ⟨-(7 : Rat) / 25, 0⟩ := point_compose.2.2.1

/-- `U U₂|0⟩`, ampiezza `|1⟩`. `Universe.Symmetry.point_compose`. -/
def compose1 : Gauss :=
  evalAt2 pointC pointS 1 0 0 pointC pointS
    (applyMat (matMul evolution evolution2) ket0).a1

example : compose1 = ⟨0, -(24 : Rat) / 25⟩ := point_compose.2.2.2

/-- `a` sui due assi. `Universe.Symmetry.point_axes`. -/
def axesAmp : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1 axesA

example : axesAmp = ⟨(9 : Rat) / 25, 0⟩ := point_axes.1

/-- `bₓ` sui due assi. `Universe.Symmetry.point_axes`. -/
def axesBx : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1 axesB.x

example : axesBx = ⟨(12 : Rat) / 25, 0⟩ := point_axes.2.1

/-- `bᵧ` sui due assi. `Universe.Symmetry.point_axes`. -/
def axesBy : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1 axesB.y

example : axesBy = ⟨-(16 : Rat) / 25, 0⟩ := point_axes.2.2.1

/-- `b_z` sui due assi. `Universe.Symmetry.point_axes`. -/
def axesBz : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1 axesB.z

example : axesBz = ⟨(12 : Rat) / 25, 0⟩ := point_axes.2.2.2.1

/-- `Uₙ Uₘ|0⟩`, ampiezza `|0⟩`. `Universe.Symmetry.point_axes`. -/
def axesNm0 : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1
    (applyMat (matMul evolution evolutionM) ket0).a0

example : axesNm0 = ⟨(9 : Rat) / 25, -(12 : Rat) / 25⟩ := point_axes.2.2.2.2.1

/-- `Uₙ Uₘ|0⟩`, ampiezza `|1⟩`. `Universe.Symmetry.point_axes`. -/
def axesNm1 : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1
    (applyMat (matMul evolution evolutionM) ket0).a1

example : axesNm1 = ⟨-(16 : Rat) / 25, -(12 : Rat) / 25⟩ := point_axes.2.2.2.2.2

/-- `Uₘ Uₙ|0⟩`, ampiezza `|0⟩`. `Universe.Symmetry.rotations_noncommute`. -/
def axesMn0 : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1
    (applyMat (matMul evolutionM evolution) ket0).a0

example : axesMn0 = ⟨(9 : Rat) / 25, -(12 : Rat) / 25⟩ := rotations_noncommute.1

/-- `Uₘ Uₙ|0⟩`, ampiezza `|1⟩`. `Universe.Symmetry.rotations_noncommute`. -/
def axesMn1 : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1
    (applyMat (matMul evolutionM evolution) ket0).a1

example : axesMn1 = ⟨(16 : Rat) / 25, -(12 : Rat) / 25⟩ := rotations_noncommute.2.1

/-- Peso `0` di `Uₙ Uₘ|0⟩`. `Universe.Symmetry.rotations_noncommute`. -/
def axesNmP0 : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1
    (columnBorn (applyMat (matMul evolution evolutionM) ket0).a0)

example : axesNmP0 = ⟨(9 : Rat) / 25, 0⟩ := rotations_noncommute.2.2.2.1

/-- Peso `1` di `Uₙ Uₘ|0⟩`. `Universe.Symmetry.rotations_noncommute`. -/
def axesNmP1 : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1
    (columnBorn (applyMat (matMul evolution evolutionM) ket0).a1)

example : axesNmP1 = ⟨(16 : Rat) / 25, 0⟩ := rotations_noncommute.2.2.2.2.1

/-- Peso `0` di `Uₘ Uₙ|0⟩`. `Universe.Symmetry.rotations_noncommute`. -/
def axesMnP0 : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1
    (columnBorn (applyMat (matMul evolutionM evolution) ket0).a0)

example : axesMnP0 = ⟨(9 : Rat) / 25, 0⟩ := rotations_noncommute.2.2.2.2.2.1

/-- Peso `1` di `Uₘ Uₙ|0⟩`. `Universe.Symmetry.rotations_noncommute`. -/
def axesMnP1 : Gauss :=
  evalAt3 pointC pointS 1 0 0 pointC pointS 0 0 1
    (columnBorn (applyMat (matMul evolutionM evolution) ket0).a1)

example : axesMnP1 = ⟨(16 : Rat) / 25, 0⟩ := rotations_noncommute.2.2.2.2.2.2

/-- `C₈(1)`. `Universe.Angle.circle_eight`. -/
def tempoC8 : Rat :=
  cosSum 8 1

example : tempoC8 = (4357 : Rat) / 8064 := circle_eight.1

/-- `S₈(1)`. `Universe.Angle.circle_eight`. -/
def tempoS8 : Rat :=
  sinSum 8 1

example : tempoS8 = (4241 : Rat) / 5040 := circle_eight.2.1

/-- Scarto `C₈² + S₈² − 1`. `Universe.Angle.circle_eight`. -/
def tempoGap8 : Rat :=
  cosSum 8 1 * cosSum 8 1 + sinSum 8 1 * sinSum 8 1 - 1

example : tempoGap8 = -(6991 : Rat) / 1625702400 := circle_eight.2.2.1

/-- Resto a `φ = 1`, `N = 8`. `Universe.Angle.circle_eight`. -/
def tempoRem8 : Rat :=
  remainder 8 1

example : tempoRem8 = (373426 : Rat) / 212837625 := circle_eight.2.2.2

/-- Scarto coseno, `N = 4`, `x = y = 1/2`. `Universe.Angle.group_half`. -/
def tempoGCos : Rat :=
  cosSum 4 ((1 : Rat) / 2 + 1 / 2) -
    (cosSum 4 (1 / 2) * cosSum 4 (1 / 2) -
      sinSum 4 (1 / 2) * sinSum 4 (1 / 2))

example : tempoGCos = (53 : Rat) / 49152 := group_half.1

/-- Scarto seno, `N = 4`, `x = y = 1/2`. `Universe.Angle.group_half`. -/
def tempoGSin : Rat :=
  sinSum 4 ((1 : Rat) / 2 + 1 / 2) -
    (sinSum 4 (1 / 2) * cosSum 4 (1 / 2) +
      cosSum 4 (1 / 2) * sinSum 4 (1 / 2))

example : tempoGSin = -(71 : Rat) / 9216 := group_half.2.1

/-- Coda di `exp(1)`, `N = 4`. `Universe.Angle.group_half`. -/
def tempoGRem : Rat :=
  sumRange (4 + 1) (2 * 4) (fun m =>
    expTerm m (((1 : Rat) / 2).abs + ((1 : Rat) / 2).abs))

example : tempoGRem = (401 : Rat) / 40320 := group_half.2.2

/-- Resto a `N = 4`, `x = 1/2`. `Universe.Angle.remainder_half`. -/
def tempoRem4 : Rat :=
  remainder 4 ((1 : Rat) / 2)

example : tempoRem4 = (401 : Rat) / 40320 := remainder_half.2.1

/-- Doppio del primo termine. `Universe.Angle.remainder_half`. -/
def tempoCap : Rat :=
  2 * expTerm (4 + 1) ((2 : Rat) * ((1 : Rat) / 2).abs)

example : tempoCap = (1 : Rat) / 60 := remainder_half.2.2

/-- `C₄(1/2)`. `Universe.Angle.angle_half`. -/
def tempoHalfC : Rat :=
  cosSum 4 ((1 : Rat) / 2)

example : tempoHalfC = (337 : Rat) / 384 := angle_half.1

/-- `S₄(1/2)`. `Universe.Angle.angle_half`. -/
def tempoHalfS : Rat :=
  sinSum 4 ((1 : Rat) / 2)

example : tempoHalfS = (23 : Rat) / 48 := angle_half.2.1

/-- Ampiezza `|0⟩` a `φ = 1/2`. `Universe.Angle.angle_half`. -/
def tempoHalf0 : Gauss :=
  evalAt (cosSum 4 ((1 : Rat) / 2)) (sinSum 4 ((1 : Rat) / 2)) 1 0 0
    (applyMat evolution ket0).a0

example : tempoHalf0 = ⟨(337 : Rat) / 384, 0⟩ := angle_half.2.2.1

/-- Ampiezza `|1⟩` a `φ = 1/2`. `Universe.Angle.angle_half`. -/
def tempoHalf1 : Gauss :=
  evalAt (cosSum 4 ((1 : Rat) / 2)) (sinSum 4 ((1 : Rat) / 2)) 1 0 0
    (applyMat evolution ket0).a1

example : tempoHalf1 = ⟨0, -((23 : Rat) / 48)⟩ := angle_half.2.2.2.1

/-- Peso `0` a `φ = 1/2`. `Universe.Angle.angle_half`. -/
def tempoHalfP0 : Gauss :=
  evalAt (cosSum 4 ((1 : Rat) / 2)) (sinSum 4 ((1 : Rat) / 2)) 1 0 0
    (bornPair (applyMat evolution ket0)).a0

example : tempoHalfP0 = ⟨(113569 : Rat) / 147456, 0⟩ := angle_half.2.2.2.2.1

/-- Peso `1` a `φ = 1/2`. `Universe.Angle.angle_half`. -/
def tempoHalfP1 : Gauss :=
  evalAt (cosSum 4 ((1 : Rat) / 2)) (sinSum 4 ((1 : Rat) / 2)) 1 0 0
    (bornPair (applyMat evolution ket0)).a1

example : tempoHalfP1 = ⟨(529 : Rat) / 2304, 0⟩ := angle_half.2.2.2.2.2.1

/-- Scarto a `φ = 1/2`, `N = 4`. `Universe.Angle.angle_half`. -/
def tempoHalfGap : Rat :=
  cosSum 4 ((1 : Rat) / 2) * cosSum 4 ((1 : Rat) / 2) +
    sinSum 4 ((1 : Rat) / 2) * sinSum 4 ((1 : Rat) / 2) - 1

example : tempoHalfGap = -((31 : Rat) / 147456) := angle_half.2.2.2.2.2.2.1

/-- Resto a `φ = 1/2`, `N = 4`. `Universe.Angle.angle_half`. -/
def tempoHalfRem : Rat :=
  remainder 4 ((1 : Rat) / 2)

example : tempoHalfRem = (401 : Rat) / 40320 := angle_half.2.2.2.2.2.2.2

/-- Testimone coseno, grado 2. `Universe.Angle.angle_add_cos`. -/
def tempoAddCos : Rat :=
  sumTo 2 (fun k =>
    cTerm k ((1 : Rat) / 2) * cTerm (2 - k) ((3 : Rat) / 5) -
      sTerm k ((1 : Rat) / 2) * sTerm (2 - k) ((3 : Rat) / 5))

example : tempoAddCos = cTerm 2 ((1 : Rat) / 2 + (3 : Rat) / 5) :=
  angle_add_cos 2 ((1 : Rat) / 2) ((3 : Rat) / 5)

/-- Testimone seno, grado 3. `Universe.Angle.angle_add_sin`. -/
def tempoAddSin : Rat :=
  sumTo 3 (fun k =>
    sTerm k ((1 : Rat) / 2) * cTerm (3 - k) ((3 : Rat) / 5) +
      cTerm k ((1 : Rat) / 2) * sTerm (3 - k) ((3 : Rat) / 5))

example : tempoAddSin = sTerm 3 ((1 : Rat) / 2 + (3 : Rat) / 5) :=
  angle_add_sin 3 ((1 : Rat) / 2) ((3 : Rat) / 5)

/-- Cella `000`. `Universe.Observer.point_cells`. -/
def cell0 : Gauss :=
  evalAt pointC pointS 1 0 0 (bornOct threeCopies).a0

example : cell0 = ⟨(729 : Rat) / 15625, 0⟩ := point_cells.1

/-- Cella `001`. `Universe.Observer.point_cells`. -/
def cell1 : Gauss :=
  evalAt pointC pointS 1 0 0 (bornOct threeCopies).a1

example : cell1 = ⟨(1296 : Rat) / 15625, 0⟩ := point_cells.2.1

/-- Cella `010`. `Universe.Observer.point_cells`. -/
def cell2 : Gauss :=
  evalAt pointC pointS 1 0 0 (bornOct threeCopies).a2

example : cell2 = ⟨(1296 : Rat) / 15625, 0⟩ := point_cells.2.2.1

/-- Cella `011`. `Universe.Observer.point_cells`. -/
def cell3 : Gauss :=
  evalAt pointC pointS 1 0 0 (bornOct threeCopies).a3

example : cell3 = ⟨(2304 : Rat) / 15625, 0⟩ := point_cells.2.2.2.1

/-- Cella `100`. `Universe.Observer.point_cells`. -/
def cell4 : Gauss :=
  evalAt pointC pointS 1 0 0 (bornOct threeCopies).a4

example : cell4 = ⟨(1296 : Rat) / 15625, 0⟩ := point_cells.2.2.2.2.1

/-- Cella `101`. `Universe.Observer.point_cells`. -/
def cell5 : Gauss :=
  evalAt pointC pointS 1 0 0 (bornOct threeCopies).a5

example : cell5 = ⟨(2304 : Rat) / 15625, 0⟩ := point_cells.2.2.2.2.2.1

/-- Cella `110`. `Universe.Observer.point_cells`. -/
def cell6 : Gauss :=
  evalAt pointC pointS 1 0 0 (bornOct threeCopies).a6

example : cell6 = ⟨(2304 : Rat) / 15625, 0⟩ := point_cells.2.2.2.2.2.2.1

/-- Cella `111`. `Universe.Observer.point_cells`. -/
def cell7 : Gauss :=
  evalAt pointC pointS 1 0 0 (bornOct threeCopies).a7

example : cell7 = ⟨(4096 : Rat) / 15625, 0⟩ := point_cells.2.2.2.2.2.2.2

/-- ⟨H⟩ prima di `Φ`, lungo `e_x`. `Universe.Symmetry.point_energy_x`. -/
def energyXBefore : Gauss :=
  evalAt pointC pointS 1 0 0 (sandwich hamiltonian ket0.a0 ket0.a1)

example : energyXBefore = 0 := point_energy_x.1

/-- ⟨H⟩ dopo `Φ`, lungo `e_x`. `Universe.Symmetry.point_energy_x`. -/
def energyXAfter : Gauss :=
  evalAt pointC pointS 1 0 0
    (sandwich hamiltonian (applyMat evolution ket0).a0 (applyMat evolution ket0).a1)

example : energyXAfter = 0 := point_energy_x.2

/-- ⟨H⟩ prima di `Φ`, lungo `e_z`. `Universe.Symmetry.point_energy_z`. -/
def energyZBefore : Gauss :=
  evalAt pointC pointS 0 0 1 (sandwich hamiltonian ket0.a0 ket0.a1)

example : energyZBefore = 1 := point_energy_z.1

/-- ⟨H⟩ dopo `Φ`, lungo `e_z`. `Universe.Symmetry.point_energy_z`. -/
def energyZAfter : Gauss :=
  evalAt pointC pointS 0 0 1
    (sandwich hamiltonian (applyMat evolution ket0).a0 (applyMat evolution ket0).a1)

example : energyZAfter = 1 := point_energy_z.2

/-- Ampiezza `|00⟩` del campione. `Universe.Interaction.point_cnot_sample`. -/
def sample00 : Gauss :=
  evalAt 0 1 1 0 0 (applyCtrl evolution (tensorPair probePair ket0)).a0

example : sample00 = ⟨(3 : Rat) / 5, 0⟩ := point_cnot_sample.1

/-- Ampiezza `|01⟩` del campione. `Universe.Interaction.point_cnot_sample`. -/
def sample01 : Gauss :=
  evalAt 0 1 1 0 0 (applyCtrl evolution (tensorPair probePair ket0)).a1

example : sample01 = 0 := point_cnot_sample.2.1

/-- Ampiezza `|10⟩` del campione. `Universe.Interaction.point_cnot_sample`. -/
def sample10 : Gauss :=
  evalAt 0 1 1 0 0 (applyCtrl evolution (tensorPair probePair ket0)).a2

example : sample10 = 0 := point_cnot_sample.2.2.1

/-- Ampiezza `|11⟩` del campione. `Universe.Interaction.point_cnot_sample`. -/
def sample11 : Gauss :=
  evalAt 0 1 1 0 0 (applyCtrl evolution (tensorPair probePair ket0)).a3

example : sample11 = ⟨-((4 : Rat) / 5), 0⟩ := point_cnot_sample.2.2.2.1

/-- Peso `|00⟩` del campione. `Universe.Interaction.point_cnot_sample`. -/
def sampleW0 : Gauss :=
  evalAt 0 1 1 0 0 (columnBorn (applyCtrl evolution (tensorPair probePair ket0)).a0)

example : sampleW0 = ⟨(9 : Rat) / 25, 0⟩ := point_cnot_sample.2.2.2.2.1

/-- Peso `|01⟩` del campione. `Universe.Interaction.point_cnot_sample`. -/
def sampleW1 : Gauss :=
  evalAt 0 1 1 0 0 (columnBorn (applyCtrl evolution (tensorPair probePair ket0)).a1)

example : sampleW1 = 0 := point_cnot_sample.2.2.2.2.2.1

/-- Peso `|10⟩` del campione. `Universe.Interaction.point_cnot_sample`. -/
def sampleW2 : Gauss :=
  evalAt 0 1 1 0 0 (columnBorn (applyCtrl evolution (tensorPair probePair ket0)).a2)

example : sampleW2 = 0 := point_cnot_sample.2.2.2.2.2.2.1

/-- Peso `|11⟩` del campione. `Universe.Interaction.point_cnot_sample`. -/
def sampleW3 : Gauss :=
  evalAt 0 1 1 0 0 (columnBorn (applyCtrl evolution (tensorPair probePair ket0)).a3)

example : sampleW3 = ⟨(16 : Rat) / 25, 0⟩ := point_cnot_sample.2.2.2.2.2.2.2

/-- Ogni punto con la sua chiave, in ordine di chiave. -/
def table : List (String × Gauss) :=
  [ ("axes.a", axesAmp),
    ("axes.bx", axesBx),
    ("axes.by", axesBy),
    ("axes.bz", axesBz),
    ("axes.mn.0", axesMn0),
    ("axes.mn.1", axesMn1),
    ("axes.mn.p0", axesMnP0),
    ("axes.mn.p1", axesMnP1),
    ("axes.nm.0", axesNm0),
    ("axes.nm.1", axesNm1),
    ("axes.nm.p0", axesNmP0),
    ("axes.nm.p1", axesNmP1),
    ("bell.00", bell00),
    ("bell.01", bell01),
    ("bell.10", bell10),
    ("bell.11", bell11),
    ("cell.0", cell0),
    ("cell.1", cell1),
    ("cell.2", cell2),
    ("cell.3", cell3),
    ("cell.4", cell4),
    ("cell.5", cell5),
    ("cell.6", cell6),
    ("cell.7", cell7),
    ("compose.0", compose0),
    ("compose.1", compose1),
    ("compose.c", composeC),
    ("compose.s", composeS),
    ("copied.coh", copiedCoh),
    ("copied.purity", copiedPur),
    ("copied.w0", copiedW0),
    ("copied.w1", copiedW1),
    ("det", bellDet),
    ("energy.x.after", energyXAfter),
    ("energy.x.before", energyXBefore),
    ("energy.z.after", energyZAfter),
    ("energy.z.before", energyZBefore),
    ("flip.coh", flipCoh),
    ("flip.purity", flipPur),
    ("idle.coh", idleCoh),
    ("idle.purity", idlePur),
    ("luders.0.0", luders00),
    ("luders.0.1", luders01),
    ("luders.1.0", luders10),
    ("luders.1.1", luders11),
    ("luders.n0", ludersN0),
    ("luders.n1", ludersN1),
    ("mid.coh", midCoh),
    ("mid.purity", midPur),
    ("p0", p0),
    ("p1", p1),
    ("purity", purityAt),
    ("repeat.0.0", repeat00),
    ("repeat.0.1", repeat01),
    ("repeat.1.0", repeat10),
    ("repeat.1.1", repeat11),
    ("sample.00", sample00),
    ("sample.01", sample01),
    ("sample.10", sample10),
    ("sample.11", sample11),
    ("sample.w0", sampleW0),
    ("sample.w1", sampleW1),
    ("sample.w2", sampleW2),
    ("sample.w3", sampleW3),
    ("tempo.add.cos", ⟨tempoAddCos, 0⟩),
    ("tempo.add.sin", ⟨tempoAddSin, 0⟩),
    ("tempo.c8", ⟨tempoC8, 0⟩),
    ("tempo.cap", ⟨tempoCap, 0⟩),
    ("tempo.gap8", ⟨tempoGap8, 0⟩),
    ("tempo.gcos", ⟨tempoGCos, 0⟩),
    ("tempo.grem", ⟨tempoGRem, 0⟩),
    ("tempo.gsin", ⟨tempoGSin, 0⟩),
    ("tempo.half.0", tempoHalf0),
    ("tempo.half.1", tempoHalf1),
    ("tempo.half.c", ⟨tempoHalfC, 0⟩),
    ("tempo.half.gap", ⟨tempoHalfGap, 0⟩),
    ("tempo.half.p0", tempoHalfP0),
    ("tempo.half.p1", tempoHalfP1),
    ("tempo.half.rem", ⟨tempoHalfRem, 0⟩),
    ("tempo.half.s", ⟨tempoHalfS, 0⟩),
    ("tempo.rem4", ⟨tempoRem4, 0⟩),
    ("tempo.rem8", ⟨tempoRem8, 0⟩),
    ("tempo.s8", ⟨tempoS8, 0⟩),
    ("u.00", u00),
    ("u.01", u01),
    ("u.10", u10),
    ("u.11", u11),
    ("undone.coh", undoneCoh),
    ("undone.purity", undonePur),
    ("v.0", v0),
    ("v.1", v1),
    ("v.conj.0", vConj0),
    ("v.conj.1", vConj1),
    ("v.w0", vW0),
    ("v.w1", vW1) ].mergeSort fun a b => decide (a.1 ≤ b.1)

end Universe.Points
