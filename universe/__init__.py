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
`Universe.Angle.cosSum` e `Universe.Angle.sinSum` sommano i termini
`cosCoeff k · φᵏ / k!` e `sinCoeff` fino al grado `N`.
`Universe.Angle.angle_add_cos` e `Universe.Angle.angle_add_sin` sono
la legge di addizione a ogni grado.

Le identità si ripartiscono per i generatori che usano. Nel libero stanno
H† = H, |z|² = re² + im², il proiettore Π₀ e la composizione con un |0⟩
fermo. Nell'ideale (gC, gN) sta un solo difetto, δ = gC + s² gN: U†U, UU†,
det U − 1, la norma per ampiezze arbitrarie, e P(0)+P(1)−1 su Φ|0⟩.
Nell'ideale (gC, gN, gA) sta ψ†(U†U)ψ − 1 sullo stato generico. gA è la
sfera delle ampiezze e resta accanto a reduce, che sbuccia solo c² e nx².
La composizione dei tempi sta in (gN); il cerchio composto in (gC, gC2);
la norma del prodotto su due assi in (gC, gN, gC2, gM).
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
e `Universe.Observer.order_irrelevant`. Wigner legge l'amico con
`cnot12`: la catena è lo stesso stato
(`Universe.Observer.chain_pointers`, `Universe.Observer.chain_is_fanout`,
`Universe.Observer.cnot12_involutive`) e l'accordo è
`Universe.Observer.chain_agree`. Disfare l'amico restituisce la coerenza
α β̄ (`Universe.Observer.friend_undone`,
`Universe.Observer.reduceSystem_product`). Dopo la copia il sistema
resta diagonale (`Universe.Observer.copy_irreversible`) e Wigner
conserva il peso di Born (`Universe.Observer.wigner_keeps_record`).
Nel punto `c = 3/5`, `s = 4/5`, `n = e_x`, con `ψ = Φ|0⟩`, disfare
l'amico dà coerenza `12/25 i` e purezza `1`
(`Universe.Observer.point_undone`). Dopo la copia la coerenza è `0`,
la purezza è `337/625` e Wigner legge `9/25` e `16/25`
(`Universe.Observer.point_copied`).
Un unitario locale sull'apparato
non cambia i pesi del sistema. Dopo `CNOT` con `|0⟩` i teoremi sono
`Universe.Observer.no_signalling_0` e `Universe.Observer.no_signalling_1`.
Per ogni stato di due qubit sono `Universe.Observer.no_signalling_any_0`
e `Universe.Observer.no_signalling_any_1`; su `genericQuad`,
`Universe.Observer.no_signalling_gen_0` e
`Universe.Observer.no_signalling_gen_1`. Per ogni stato di tre qubit,
`Universe.Observer.no_signalling_wigner` e
`Universe.Observer.no_signalling_friend` dicono lo stesso di un unitario
sul qubit di Wigner e su quello dell'amico. Per ogni `n` e ogni coppia di
qubit distinti, lo stesso è `Universe.Qubits.no_signalling_at`.
`Universe.Qubits.cnotFrom0` copia il sistema su un altro qubit.
`Universe.Qubits.fanout` li applica tutti su `|ψ⟩ ⊗ |0…0⟩`:
`fanout_ghz` è `α|0…0⟩ + β|1…1⟩`, `fanout_agree` azzera il peso
delle celle in cui due qubit differiscono, e `fanout_decoherence`
rende il sistema diagonale con `bornPair`.

`U` commuta con `H` nell'anello libero:
`Universe.Symmetry.evolution_commutes_hamiltonian`. L'energia
`⟨ψ|H|ψ⟩` è conservata nell'ideale `(gC, gN)`, per ogni ampiezza:
`Universe.Symmetry.energy_conserved`. Nel punto `c = 3/5`, `s = 4/5`
lo stato `|0⟩` ha energia `0` lungo `e_x` e `1` lungo `e_z`, prima e
dopo `Φ` (`Universe.Symmetry.point_energy_x`,
`Universe.Symmetry.point_energy_z`).
`Universe.Symmetry.conj_evolution_law` e `Universe.Symmetry.conj_born_law`
portano il cambio di base su `V = U`, modulo `(gC, gN)`.
`Universe.Symmetry.point_compose` valuta l'angolo composto.
`Universe.Symmetry.evolution_compose_axes` è il prodotto su due assi,
`a I − i (b·σ)`, nell'anello libero. `a² + |b|² − 1` sta in
`(gC, gN, gC2, gM)` (`Universe.Symmetry.compose_axes_norm`); `gM` resta
fuori da `reduce`. Nel punto `n = e_x`, `m = e_z`,
`Universe.Symmetry.point_axes` valuta `a`, `b` e `Uₙ Uₘ |0⟩`.
`Universe.Symmetry.rotations_noncommute` dice che l'altro ordine differisce
sull'ampiezza di `|1⟩`, con gli stessi pesi di Born. `evalAt3` legge
`mx my mz`.

`G = |1⟩⟨1| ⊗ H` soddisfa `G³ = G`
(`Universe.Interaction.generator_cube`), con i coefficienti di
`Universe.Series.expCoeff_idem`. La forma chiusa è l'evoluzione
controllata `Universe.Interaction.controlled_from_hamiltonian`.
Nel punto `c = 0`, `s = 1`, `n = e_x` è `CNOT` seguito dalla fase `−i`
(`Universe.Interaction.cnot_point`); la fase esce dai pesi di Born
(`Universe.Interaction.cnot_point_born`). Con l'apparato in `|0⟩` la
coerenza del sistema ridotto è `α β̄ · conj(⟨0|U|0⟩)`
(`Universe.Interaction.partial_coherence`) e la diagonale è il peso di
Born modulo `(gC, gN)` (`Universe.Interaction.partial_diagonal`). I tre
punti lungo `e_x` sono `Universe.Interaction.point_partial_idle`,
`Universe.Interaction.point_partial_mid` e
`Universe.Interaction.point_partial_flip`.
`Universe.Interaction.luders` è la lettura del puntatore dopo `CNOT`:
`(α, 0)` e `(0, β)`, con norme i pesi di Born.
`Universe.Interaction.repeatable` ripete l'esito su un apparato fresco.
Nel punto le norme sono `9/25` e `16/25`
(`Universe.Interaction.point_luders`,
`Universe.Interaction.point_repeatable`).

Il primo mondo è un qubit. I teoremi si eseguono con `python -m universe`.
"""

from universe.worlds.qubit import QubitUniverse

__all__ = ["QubitUniverse"]
