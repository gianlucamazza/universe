"""Kernel di una rappresentazione esatta dell'universo.

Un universo è una tripla (X, Φ, Obs):

- X è l'ontologia: lo spazio degli stati e il modo in cui i sistemi si compongono.
- Φ è la dinamica: la legge, qui un operatore unitario generato da un'Hamiltoniana.
- Obs è l'epistemologia: le osservabili che un osservatore interno può estrarre.

Due rappresentazioni sono lo stesso universo quando un isomorfismo commuta con Φ
e con Obs. «Perfetto» vuol dire che quel diagramma commuta e che gli invarianti
sono teoremi. Le identità polinomiali hanno resto zero nel quoziente
c² + s² = 1, |n| = 1, e quel resto esibisce i cofattori nell'anello libero.
Il collasso di exp(−i φ a) è Universe.Series.expCoeff quando a² = 1.
L'istanza su questo qubit è Universe.Qubit.expCoeff_hamiltonian.

Le identità si ripartiscono per i generatori che usano. Nel libero stanno
H† = H, |z|² = re² + im², il proiettore Π₀ e la composizione con un |0⟩
fermo. Nell'ideale (gC, gN) sta un solo difetto, δ = gC + s² gN: U†U, UU†,
det U − 1, la norma per ampiezze arbitrarie, e P(0)+P(1)−1 su Φ|0⟩.
Nell'ideale (gC, gN, gA) sta ψ†(U†U)ψ − 1 sullo stato generico. gA è la
sfera delle ampiezze e resta accanto a reduce, che sbuccia solo c² e nx².
La nota è papers/qubit.md. L'indice è il README.

Il primo mondo è un qubit. I teoremi si eseguono con `python -m universe`.
"""

from universe.worlds.qubit import QubitUniverse

__all__ = ["QubitUniverse"]
