"""Kernel di una rappresentazione esatta dell'universo.

Un universo è una tripla (X, Φ, Obs):

- X è l'ontologia: lo spazio degli stati e il modo in cui i sistemi si compongono.
- Φ è la dinamica: la legge, qui un operatore unitario generato da un'Hamiltoniana.
- Obs è l'epistemologia: le osservabili che un osservatore interno può estrarre.

Due rappresentazioni sono lo stesso universo quando un isomorfismo commuta con Φ
e con Obs. «Perfetto» vuol dire che quel diagramma commuta e che gli invarianti
sono teoremi. Le due parentesizzazioni di tre qubit sono quell'isomorfismo:
`Universe.Composition.tensor_assoc` sulle ampiezze, `tensor_assoc_ui` per Φ sul
primo fattore, `tensor_assoc_obs` per il modulo quadro di ogni cella.
L'argomento è `researches/associazione.md`. Le identità polinomiali hanno resto
zero nel quoziente c² + s² = 1, |n| = 1, e quel resto esibisce i cofattori
nell'anello libero.
Il collasso di exp(−i φ a) è Universe.Series.expCoeff quando a² = 1.
L'istanza su questo qubit è Universe.Qubit.expCoeff_hamiltonian.

Le identità si ripartiscono per i generatori che usano. Nel libero stanno
H† = H, |z|² = re² + im², il proiettore Π₀ e la composizione con un |0⟩
fermo. Nell'ideale (gC, gN) sta un solo difetto, δ = gC + s² gN: U†U, UU†,
det U − 1, la norma per ampiezze arbitrarie, e P(0)+P(1)−1 su Φ|0⟩.
Nell'ideale (gC, gN, gA) sta ψ†(U†U)ψ − 1 sullo stato generico. gA è la
sfera delle ampiezze e resta accanto a reduce, che sbuccia solo c² e nx².
Se p sta in (gC, gN), Universe.Dynamics.reduce_complete dice che ogni
coefficiente del resto di reduce è zero. I cofattori sono un testimone.
La nota è papers/qubit.md. L'argomento della divisione è
researches/divisione-monica.md. L'indice è il README.

CNOT scambia |10⟩ e |11⟩. Su |ψ⟩ ⊗ |0⟩ produce α|00⟩ + β|11⟩. Il determinante
di un prodotto è zero nell'anello libero; nel punto razionale vale −12/25 i,
quindi CNOT(Φ|0⟩ ⊗ |0⟩) non è un prodotto. I teoremi sono
`Universe.Observer.cnot_involutive`, `Universe.Observer.cnot_norm`,
`Universe.Observer.product_det`, `Universe.Observer.entangled_det`,
`Universe.Observer.point_entangled` e `Universe.Observer.point_not_product`.
La traccia parziale dopo CNOT è diagonale: i pesi sono quelli di Born, e
l'apparato li legge su Φ|ψ⟩. Nel punto razionale la purezza del sistema
ridotto è 337/625. I teoremi sono `Universe.Observer.decoherence`,
`Universe.Observer.pointer_born` e `Universe.Observer.point_purity`.
Due apparati, accoppiati con CNOT in entrambi gli ordini, danno
α|000⟩ + β|111⟩: le celle 1–6 hanno peso zero. I teoremi sono
`Universe.Observer.two_pointers`, `Universe.Observer.observers_agree`
e `Universe.Observer.order_irrelevant`. Un unitario locale sull'apparato
non cambia i pesi del sistema. Dopo `CNOT` con `|0⟩` i teoremi sono
`Universe.Observer.no_signalling_0` e `Universe.Observer.no_signalling_1`.
Per ogni stato di due qubit sono `Universe.Observer.no_signalling_any_0`
e `Universe.Observer.no_signalling_any_1`; su `genericQuad`,
`Universe.Observer.no_signalling_gen_0` e
`Universe.Observer.no_signalling_gen_1`.

`U` commuta con `H` nell'anello libero:
`Universe.Symmetry.evolution_commutes_hamiltonian`. L'energia
`⟨ψ|H|ψ⟩` è conservata nell'ideale `(gC, gN)`, per ogni ampiezza:
`Universe.Symmetry.energy_conserved`. Nel punto `c = 3/5`, `s = 4/5`
lo stato `|0⟩` ha energia `0` lungo `e_x` e `1` lungo `e_z`, prima e
dopo `Φ` (`Universe.Symmetry.point_energy_x`,
`Universe.Symmetry.point_energy_z`).

Il primo mondo è un qubit. I teoremi si eseguono con `python -m universe`.
"""

from universe.worlds.qubit import QubitUniverse

__all__ = ["QubitUniverse"]
