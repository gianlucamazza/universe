/-
Tabella dei punti razionali.

Ogni voce è il membro sinistro del teorema che la dimostra.
Un `example` la lega al valore dimostrato: il numero stampato e il
numero dimostrato sono lo stesso termine. `lake exe points` stampa
`chiave re im`.
-/
import Universe.Epistemology

namespace Universe.Points

open Universe.Ring
open Universe.Epistemology
open Universe.Qubit

/-- P(0) nel punto. `Universe.Epistemology.point_prob0`. -/
def p0 : Gauss :=
  evalAt pointC pointS 1 0 0 (columnBorn (specPoly keepX evolution.a00))

example : p0 = ⟨(9 : Rat) / 25, 0⟩ := point_prob0

/-- P(1) nel punto. `Universe.Epistemology.point_prob1`. -/
def p1 : Gauss :=
  evalAt pointC pointS 1 0 0 (columnBorn (specPoly keepX evolution.a10))

example : p1 = ⟨(16 : Rat) / 25, 0⟩ := point_prob1

/-- Ogni punto con la sua chiave, in ordine di chiave. -/
def table : List (String × Gauss) :=
  [("p0", p0), ("p1", p1)].mergeSort fun a b => decide (a.1 ≤ b.1)

end Universe.Points
