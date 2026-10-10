/-
Kernel formale. Il corrispondente eseguibile sta nel pacchetto Python `universe`.

`Universe.Ring` è lo scalare `ℚ(i)`.
`Universe.Quotient` è il quoziente `c² + s² = 1`, `|n| = 1`, con cofattori.
`gA`, nello stesso file, è la sfera delle ampiezze e non entra in `reduce`.
`Universe.Series` è il collasso di `exp(-i φ a)` quando `a² = 1`.
`Universe.Dynamics` è l'algebra delle matrici su quel quoziente.
`Universe.Qubit` istanzia `expCoeff` sull'Hamiltoniana e prova `U†U`, `UU†`,
`det U − 1` e la norma per ampiezze arbitrarie, con cofattori `gC + s² · gN`.
`Universe.Ontology` è X, la composizione dei sistemi.
-/
import Universe.Dynamics
import Universe.Ontology
import Universe.Qubit
import Universe.Quotient
import Universe.Ring
import Universe.Series
