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

Il primo mondo è un qubit. I teoremi si eseguono con `python -m universe`.
"""

from universe.worlds.qubit import QubitUniverse

__all__ = ["QubitUniverse"]
