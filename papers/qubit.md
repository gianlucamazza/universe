# Un qubit, tre livelli di uguaglianza

Nota sul primo mondo del kernel `universe`. I nomi in corpo di testo sono lemmi di Lean 4.34.1, nel pacchetto `Universe`, o certificati di `python -m universe`. L'indice riga per riga è il README. Qui si registra come le identità si ripartiscono.

## 1. La tripla

Un universo è `(X, Φ, Obs)`. `X` è lo spazio degli stati e la composizione. `Φ` è la legge. `Obs` è ciò che un osservatore interno estrae. Due descrizioni sono lo stesso universo quando un isomorfismo commuta con `Φ` e con `Obs`.

Le due parentesizzazioni di tre qubit sono quell'isomorfismo. `Universe.Composition.tensor_assoc` identifica le ampiezze di `((|ψ⟩ ⊗ |φ⟩) ⊗ |χ⟩)` e di `(|ψ⟩ ⊗ (|φ⟩ ⊗ |χ⟩))`, con indice `4·i + 2·j + k`. `tensor_assoc_ui` porta `(U ⊗ I ⊗ I)` sul primo fattore. `tensor_assoc_obs` identifica il modulo quadro di ogni cella. L'argomento, con la tabella delle otto celle, è `researches/associazione.md`.

Associazione e poi `U` sul primo fattore è la stessa lista di `U` e poi associazione.

![Le due parentesizzazioni e U sul primo fattore](figures/quadrato.svg)

`tensor_assoc_obs` identifica `z · conj(z)` su ogni cella dei due stati prima di `U`. I due stati dopo `U` hanno gli stessi pesi perché quegli stati sono uguali.

Il primo mondo è un qubit finito. `X = ℂ²`. L'Hamiltoniana è `H = n·σ`, con

```
Y = [[0, −i], [i, 0]].
```

La fase è `φ = ωt/2`. Sul quoziente `c² + s² = 1` e `|n| = 1` la forma chiusa è

```
U = c I − i s H.
```

`c` e `s` sono indeterminate del quoziente del cerchio. Il collasso della serie che autorizza quella scrittura è `Universe.Qubit.expCoeff_hamiltonian`: `H² = I` nel quoziente, quindi i coefficienti di `φⁿ/n!` in `exp(−iφ H)` sono quelli di `cos φ · I + (−i sin φ) · H`. `Obs` è la misura proiettiva nella base computazionale. La probabilità di un'ampiezza è il suo modulo quadro. `Universe.Observer.pointer_born` ricava quegli stessi pesi come diagonale dell'apparato, dopo `CNOT` su `Φ|ψ⟩ ⊗ |0⟩`.

Il certificato eseguibile stampa 70 identità. Il testo formale non è un'estrazione del testo Python, né il contrario. I due testi si citano. Dove calcolano polinomi diversi, la nota lo dice.

## 2. L'anello

Lo scalare è `ℚ(i)`, `Universe.Ring`. Un polinomio è una lista di termini

```
coefficiente · c^c s^s nx^nx ny^ny nz^nz ar^ar ai^ai br^br bi^bi a2r^a2r a2i^a2i a3r^a3r a3i^a3i c2^c2 s2^s2 mx^mx my^my mz^mz.
```

Due generatori del quoziente, con cofattori nell'anello libero:

```
gC = c² + s² − 1,
gN = nx² + ny² + nz² − 1.
```

`Universe.Quotient.reduce` sbuccia solo `c²` e `nx²`, in quest'ordine sulle variabili e con `nx` prima di `ny` e `nz` nel secondo quadrato:

```
c²  = (1 − s²) + gC,
nx² = (1 − ny² − nz²) + gN.
```

`reduce_sound` dice che, per ogni polinomio e ogni monomio, i coefficienti di `p` coincidono con quelli di `resto + f·gC + g·gN`. Se il resto ha tutti i coefficienti zero, `p` sta nell'ideale `(gC, gN)`. Il testimone esibisce l'appartenenza. `Universe.Dynamics.reduce_complete` è il converso per questo `reduce`: se `p` sta nell'ideale, ogni coefficiente del resto è zero. L'enunciato è su `coeffOf`: una lista non vuota può cancellarsi. I cofattori non sono unici.

`gC` è monico di grado 2 in `c`, `gN` in `nx`, e le due variabili sono disgiunte. `reduceC` sbuccia solo `c²`. Se `f · gC` non ha grado `≥ 2` in `c`, la discesa sulle fette `sliceC` a partire da `cBound` annulla ogni coefficiente di `f`. Lo stesso vale per `gN` e `sliceNx`. Un resto `normal` nell'ideale si divide in `c`, e le due discese lo azzerano. `mul_gC_low` e `mul_gN_low` stanno in `Dynamics`, perché una fetta a coefficienti zero può non essere la lista vuota. Il motore delle fette sta in `Quotient`. `reduce_gC_rem` e `reduce_gN_rem` restano il calcolo diretto. L'argomento per esteso è `researches/divisione-monica.md`. Il teorema è su `reduce` di Lean.

`gA = ar² + ai² + br² + bi² − 1` è definito nello stesso file. È il terzo generatore, la sfera delle ampiezze. `reduce` lo lascia dov'è.

## 3. La legge è un difetto

Sul libero, `hamiltonian_dagger` è `H† = H`. Nel quoziente, `hamiltonian_sq` dà la diagonale di `H² − I` uguale a `gN`, con cofattore la costante `1`, e il fuori diagonale a coefficienti zero. `hamiltonian_cube` e `hamiltonian_fourth` seguono da `H² = I` per moltiplicazione delle matrici quoziente. `expCoeff_hamiltonian` è l'istanza che scrive `U`.

Le quattro identità di conservazione hanno gli stessi cofattori. Sia

```
δ = gC + s² gN.
```

Allora `evolution_unitary`, `evolution_unitary_rev` e `evolution_det` dicono che `U†U − I`, `UU† − I` e `det U − 1` sono `δ` sulle entrate diagonali, nel senso dell'ideale `(gC, gN)`. Per ogni coppia di ampiezze, `evolution_norm` dice che il sandwich `ψ†(U†U)ψ − ‖ψ‖²` sta nello stesso ideale. `literal_sandwich` dice che, per ogni matrice e ogni coppia di ampiezze, il modulo letterale `|γ₀|² + |γ₁|²` con `γ = Uψ` ha gli stessi coefficienti di `ψ†(U†U)ψ`. `born_norm` identifica `‖ψ‖²` nell'ordine `z · conj(z)` con `normAmp`. `literal_evolution_norm` trasporta l'ideale sul polinomio `‖Uψ‖² − ‖ψ‖²` che il certificato riduce.

`Φ|0⟩` è la prima colonna di `U`, `(c − i s nz, s ny − i s nx)`. Le ampiezze di `|0⟩` sono `1` e `0`. `ground_prob_sum` mette `P(0) + P(1) − 1` di quello stato nello stesso ideale, con gli stessi cofattori di `δ`. La sfera qui non compare.

`U` commuta con `H` nel libero: `UH` e `HU` sono entrambi `c H − i s H²`, `Universe.Symmetry.evolution_commutes_hamiltonian`. Quindi `U†HU = U†UH`, e `energy_conserved` mette `⟨Uψ|H|Uψ⟩ − ⟨ψ|H|ψ⟩` in `(gC, gN)` per ogni coppia di ampiezze: l'energia è conservata, con gli stessi cofattori di `δ`. `point_energy_x` e `point_energy_z` valutano `⟨0|H|0⟩` nel punto: `0` lungo x, `1` lungo z, prima e dopo `Φ`.

Il tempo si compone. `evolution_compose` mette `U(c₁, s₁) U(c₂, s₂) − U(c₁c₂ − s₁s₂, s₁c₂ + c₁s₂)` nell'ideale del solo `gN` (`inIdealN`): la legge di gruppo usa `H² = I` e non il cerchio. `compose_circle` mette `c² + s² − 1` in `(gC, gC2)` con cofattori `c₂² + s₂²` e `1` (`inIdealCircle`); `gC2 = c2² + s2² − 1` resta fuori da `reduce`, come `gA`. Il punto `(3/5, 4/5)` due volte è `(−7/25, 24/25)`, e `U²|0⟩ = −7/25 |0⟩ − 24/25 i |1⟩`: `evalAt2`, che legge anche `c2 s2` e coincide con `evalAt` dove quei due esponenti sono nulli (`evalAt2_agrees`), dà lo stesso valore in Lean (`point_compose`).

![Il tempo si compone](figures/tempo.svg)

Due assi. `pauli_product` dà `(n·σ)(m·σ) = (n·m) I + i (n×m)·σ` nel libero, per polinomi qualsiasi. Con `evolutionM`, il passo sull'asse `m`, `evolution_compose_axes` dà `U(c₁, s₁, n) U(c₂, s₂, m) = a I − i (b·σ)` nel libero, con `a = c₁c₂ − s₁s₂ (n·m)` e `b = s₁c₂ n + c₁s₂ m + s₁s₂ (n×m)`: la legge sullo stesso asse chiedeva `gN`, questa nessuna regola. `compose_axes_same` ritrova quella legge con `m = n`, modulo `gN`. `axes_norm_free` è l'identità dei quattro quadrati, `a² + |b|² = (c₁² + s₁²|n|²)(c₂² + s₂²|m|²)`, e `compose_axes_norm` mette `a² + |b|² − 1` in `(gC, gN, gC2, gM)` (`inIdeal4`) con cofattori `R₂`, `s₁² R₂`, `1`, `s₂²`, dove `R₂ = c₂² + s₂²|m|²`; `gM = mx² + my² + mz² − 1` resta fuori da `reduce`. `evalAt3` legge anche `mx my mz` e coincide con `evalAt2` dove sono nulli (`evalAt3_agrees`). In `n = eₓ`, `m = e_z`, `(3/5, 4/5)` due volte, `a = 9/25` e `b = (12/25, −16/25, 12/25)` (`point_axes`). `rotations_noncommute`: `UₙUₘ|0⟩` e `UₘUₙ|0⟩` hanno la stessa ampiezza su `|0⟩`, `9/25 − 12/25 i`, e su `|1⟩` `−16/25 − 12/25 i` e `16/25 − 12/25 i`; i pesi sono `9/25` e `16/25` in entrambi gli ordini.

![Due assi: l'ordine cambia lo stato, non i pesi](figures/assi.svg)

Il principio d'identità del nucleo ha un caso base. Per ogni matrice `V` con `V†V = I` nel libero, `conj_evolution` dà `V(Uψ) = (VUV†)(Vψ)` e `conj_born` dà ai pesi di `Vψ` nella base `V|k⟩` i valori di `ψ`: la descrizione ruotata evolve e osserva come l'originale. `conj_inverse` ricava `VV† = I`. Con `V†V = I` modulo `(gC, gN)` gli stessi enunciati valgono nell'ideale (`conj_evolution_rel`, `conj_born_rel`), e si applicano alla legge simbolica, `V = U` (`conj_evolution_law`, `conj_born_law`). Nel punto, `V(U|0⟩) = −7/25 |0⟩ − 24/25 i |1⟩` (`point_conj_evolution`, `point_conj_born`).

## 4. L'osservazione

Tre fatti sono liberi, prima di ogni quoziente.

`modulus_squares` e `modulus_imag_zero`: per ogni polinomio, `z · conj(z)` ha i coefficienti di `re(z)² + im(z)²`, e ogni coefficiente ha parte immaginaria zero. `columnBorn_real` è lo stesso enunciato per ogni peso di Born. `ground_prob_real` è il caso di `Φ|0⟩`.

`projector_born`: `Π₀ = diag(1, 0)` e `⟨ψ|Π₀|ψ⟩ = |α|²` per ogni coppia di ampiezze. Il sandwich del proiettore e il modulo di `α` hanno gli stessi coefficienti.

La sfera entra su uno stato generico `(ar + i ai, br + i bi)`. `sphere_prob_sum` mette `ψ†(U†U)ψ − 1` nell'ideale `(gC, gN, gA)`, con tre cofattori. Il predicato è `inIdeal3`. È nuovo: non estende `inIdeal` e non aggiunge una regola a `reduce`. `literal_sphere` trasporta gli stessi tre cofattori sul modulo letterale `‖Uψ‖² − 1`: `literal_sandwich` dà ai due polinomi gli stessi coefficienti. Il certificato Python esibisce quell'appartenenza con `certify_extra`, e `gA` resta generatore accanto alle due regole dell'anello. Senza `gA` quel resto non è zero.

La ripartizione è questa. La conservazione della norma, per ampiezze arbitrarie, vive in `(gC, gN)`. La somma delle probabilità sullo stato generico vive in `(gC, gN, gA)`. La somma sullo stato fondamentale evolve torna a `δ`, perché la sua norma è già `1` nel libero.

## 5. Assi e punto razionale

`keepX` e `keepZ` sono omomorfismi di valutazione sui monomi. `keepX` tiene un monomio quando `ny = nz = 0` e azzera l'esponente di `nx`. `keepZ` tiene un monomio quando `nx = ny = 0` e azzera l'esponente di `nz`. Un monomio con un altro esponente di asse positivo viene scartato. `keepX_mul` e `keepZ_mul` commutano con il prodotto di monomi. `spec_append` commuta con la somma per ogni scelta. `specX_conj`, `specZ_conj`, `specX_pmul` e `specZ_pmul` fanno di `spec` un omomorfismo d'anello, nel senso di `polySame` sul prodotto. `spec_columnBorn` ne deduce che specializzare un peso di Born è il peso di Born dell'ampiezza già specializzata.

Lungo x, `axis_x_prob0` è `|c|² − (1 − s²) = gC` sull'ampiezza specializzata, e `axis_x_born0` è lo stesso enunciato su `spec keepX groundP0`. `axis_x_prob1` e `axis_x_born1` danno `|-i s|² = s²` a partire da `groundP1`. `axis_x_gn` azzera i coefficienti di `gN`. Lungo z, `axis_z_prob1` e `axis_z_born1` dicono che la seconda ampiezza e il suo peso sono il polinomio zero, quindi `|0⟩` è autostato. `axis_z_prob0` e `axis_z_born0` sono `|c − i s|² − 1 = gC`. `axis_z_gn` azzera i coefficienti di `gN` anche lungo z.

Il certificato Python sostituisce `nx`, `ny`, `nz` nei pesi di Born già calcolati per `Φ|0⟩` e confronta le forme ridotte: lungo x, `P(0) = 1 − s²` e `P(1) = s²`; lungo z, `P(0) = 1` e `P(1) = 0`. Quel polinomio è `spec` di `groundP0` e di `groundP1`. `reduce` sbuccia ancora solo `c²` e `nx²`.

Il punto `c = 3/5`, `s = 4/5`, `n = eₓ` è un corollario. `point_prob0` e `point_prob1` valutano i pesi specializzati e ottengono `9/25` e `16/25`, i quadrati di `3/5` e `4/5`. `point_gC` e `point_gN` sono i due vincoli in `ℚ`. `point_unitary` valuta `δ` in quel punto e ottiene zero. La chiusura è `ext`, poi `simp`, poi `grind` sui razionali di Gauss. Il certificato Python moltiplica la matrice numerica e legge gli stessi valori sui moduli della prima colonna.

| lettura                  | P(0)   | P(1)  |
| ------------------------ | ------ | ----- |
| lungo x                  | 1 − s² | s²    |
| lungo z                  | 1      | 0     |
| c = 3/5, s = 4/5, n = eₓ | 9/25   | 16/25 |

![Il cerchio e il punto 3/5, 4/5](figures/cerchio.svg)

I coefficienti espongono la ripartizione delle sezioni 3 e 4: chi paga ogni identità, e con quale generatore. Il punto razionale è un corollario di quella ripartizione.

## 6. Composizione

L'indice di `|i⟩ ⊗ |k⟩` è `right · i + k`, `Universe.Composition.tensorIndex`. È il passo binario di `Universe.Ontology.tensorIndexAssoc`.

`ground_tensor`: `|0⟩ ⊗ |0⟩` ha ampiezza `1` nella cella `0` e il polinomio zero nelle altre tre.

Per ogni matrice 2×2 e ogni coppia di ampiezze, `kronecker_ui_gen` è

```
(U ⊗ I)(|ψ⟩ ⊗ |φ⟩) = (U|ψ⟩) ⊗ |φ⟩.
```

È un'uguaglianza di liste: la distributività a sinistra di `pmul`. `kronecker_ui` è il caso `|φ⟩ = |0⟩`. `marginal_left_gen` dice che il marginale sinistro ha i coefficienti di `‖φ‖² · Pᵢ(U|ψ⟩)`. `normPair_ket0` dice che, per `|φ⟩ = |0⟩`, `‖φ‖²` è la costante `1` nell'anello libero, e `marginal_ui_from_gen` ritrova `marginal_ui`.

`kronecker_iu_gen` scambia i fattori. Il prodotto sta nel fattore destro, quindi l'uguaglianza è `quadSame`, gli stessi coefficienti. `marginal_right_gen` è `‖ψ‖² · Pᵢ(U|φ⟩)`. Con il fattore fermo uguale a `|0⟩` si ritrova `marginal_iu`.

Sul fattore generico `(ar + i ai, br + i bi)`, `marginal_left_sphere` e `marginal_right_sphere` tolgono il fattore `‖φ‖²` con cofattore esplicito `gA` e cofattori nulli per `gC` e `gN`. `gA` resta fuori da `reduce`.

Su tre qubit, `tensorIndex_assoc_qubit` è `tensorIndexAssoc` con dimensioni `2` e `2`. `tensor_assoc` è l'uguaglianza di liste fra le due parentesizzazioni. La cella `(i, j, k)` vale `ψᵢ φⱼ χₖ` in entrambe, e l'indice è `4·i + 2·j + k`. `assoc_row` fa attraversare a una riga di `U` i due prodotti, con `pmul_assoc` e `pmul_append_left`. `applyUII` agisce sul bit alto: la prima riga di `U` sulle celle `0`–`3`, la seconda sulle celle `4`–`7`. `tensor_assoc_ui` è `(U ⊗ I ⊗ I)((ψ ⊗ φ) ⊗ χ) = ((Uψ) ⊗ φ) ⊗ χ`. `tensor_assoc_ui_right` è la stessa azione sulla parentesizzazione destra. `bornOct` applica `columnBorn` a ogni cella, e `tensor_assoc_obs` identifica i due pesi.

| cella | i   | j   | k   | ampiezza |
| ----- | --- | --- | --- | -------- |
| 0     | 0   | 0   | 0   | ψ₀ φ₀ χ₀ |
| 1     | 0   | 0   | 1   | ψ₀ φ₀ χ₁ |
| 2     | 0   | 1   | 0   | ψ₀ φ₁ χ₀ |
| 3     | 0   | 1   | 1   | ψ₀ φ₁ χ₁ |
| 4     | 1   | 0   | 0   | ψ₁ φ₀ χ₀ |
| 5     | 1   | 0   | 1   | ψ₁ φ₀ χ₁ |
| 6     | 1   | 1   | 0   | ψ₁ φ₁ χ₀ |
| 7     | 1   | 1   | 1   | ψ₁ φ₁ χ₁ |

Il certificato Python confronta i polinomi ridotti nel caso `|φ⟩ = |0⟩`, anche quando l'altro fattore è lo stato generico. `|00⟩` è il caso `α = 1`, `β = 0` delle stesse due righe, e resta nel dettaglio. La riga di associatività usa due anelli. Gli indici stanno su `(i, j, k, nb, nc)`. Ampiezze e `(U ⊗ I ⊗ I)` stanno su `(u00, u01, u10, u11, a0, a1, b0, b1, c0, c1)`. Il dettaglio cita `tensor_assoc`, `tensor_assoc_ui` e `tensor_assoc_obs`.

Tre copie di `Φ|0⟩`, valutate in `c = 3/5`, `s = 4/5`, `n = eₓ`, riempiono le otto celle. Il peso è `(9/25)` per ogni bit `0` e `(16/25)` per ogni bit `1`. Le due parentesizzazioni danno gli stessi pesi e la somma è `1`. È la stessa riga del punto razionale: Lean ha `point_prob0` e `point_prob1` sul singolo fattore, il certificato valuta il triplo tensore. Quella misura non aggiunge una riga.

![Otto celle di tre copie di Φ|0⟩](figures/celle.svg)

| cella | bit | peso       |
| ----- | --- | ---------- |
| 0     | 000 | 729/15625  |
| 1     | 001 | 1296/15625 |
| 2     | 010 | 1296/15625 |
| 3     | 011 | 2304/15625 |
| 4     | 100 | 1296/15625 |
| 5     | 101 | 2304/15625 |
| 6     | 110 | 2304/15625 |
| 7     | 111 | 4096/15625 |

## 7. L'osservatore

`Obs` era un assioma. Qui diventa la diagonale di un sottosistema. Il modulo è `Universe.Observer`; ogni enunciato vale per ogni coppia di ampiezze, nell'anello libero, salvo dove è detto.

`applyCNOT` scambia le celle `|10⟩` e `|11⟩`. `cnot_involutive` è `CNOT² = I`, come uguaglianza di liste. `cnot_norm` conserva la somma dei quattro pesi di Born. `cnot_ket0` è

```
CNOT(|ψ⟩ ⊗ |0⟩) = α|00⟩ + β|11⟩.
```

`quadDet` è `a₀a₃ − a₁a₂`. `product_det` lo annulla su ogni prodotto: è la commutatività e l'associatività di `pmul` nei coefficienti. `entangled_det` dà `α β` dopo `CNOT`. Nel punto `c = 3/5`, `s = 4/5`, `n = eₓ`, `point_bell` valuta le quattro celle in `3/5`, `0`, `0`, `−4/5 i`, `point_entangled` dà `−12/25 i`, e `point_not_product` dice che nessuna coppia di vettori di `ℚ(i)` ha quel tensore.

![CNOT e la griglia delle ampiezze](figures/cnot.svg)

L'interazione non è scritta a mano. `Universe.Interaction` prende il generatore `G = |1⟩⟨1| ⊗ (n·σ)`: `G² = |1⟩⟨1| ⊗ I` modulo `gN` e `G³ = G` (`generator_cube`). `Universe.Series.expCoeff_idem` è il secondo collasso della serie: se `a³ = a`, i coefficienti di `exp(−iφ a)` sono quelli di `(1 − a²) + cos φ · a² − i sin φ · a`. Su `G` quella forma è `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` (`controlled_from_hamiltonian`). Nel punto `c = 0`, `s = 1`, `n = eₓ` vale `U = −i X`, e `cnot_point` identifica l'evoluzione controllata con `CNOT` seguito dalla fase `−i` sul `|1⟩` del controllo. `cnot_point_born` mostra che la fase esce da ogni peso di Born: i teoremi che seguono valgono per l'interazione dinamica.

`reduceLeft` è la traccia parziale sull'apparato, `reduceRight` sul sistema. `reduceLeft_diag` dice che la diagonale è `marginalLeft`, per definizione. `reduce_product` dà `‖φ‖² |ψ⟩⟨ψ|` su un prodotto: senza interazione il sistema resta puro. `coherence_before` dà `α β̄` fuori diagonale prima di `CNOT`. `decoherence` dice che dopo `CNOT` i due termini fuori diagonale sono il polinomio zero e la diagonale è `bornPair ψ`. `pointer_born` è lo stesso fatto letto sull'apparato, per `Φ|ψ⟩`: la diagonale dello stato ridotto dell'apparato è `bornPair (Φ|ψ⟩)`. È l'enunciato che prende il posto dell'assioma.

`pointer_born` non usa né `δ` né `gA`. I pesi che l'apparato legge sono quelli di `Φ|ψ⟩`, normalizzati o no; la loro somma è il fatto della sezione 4.

`purity` è `Tr(ρ²)`. `purity_before` dà `‖ψ‖⁴` su `|ψ⟩⟨ψ|`. `purity_after` dà `|α|⁴ + |β|⁴` dopo `CNOT`. `purity_sphere` mette `1 − purezza − 2|α|²|β|²` nell'ideale `(gC, gN, gA)`, sullo stato generico, con il solo cofattore di `gA`. `point_purity` vale `337/625` nel punto, minore di `1`: lo stato ridotto è misto. Le valutazioni passano per `Universe.Evaluation`, dove `eval_polySame`, `eval_pmul` ed `eval_conj` fanno di `evalAt` un omomorfismo.

![Lo stato ridotto prima e dopo CNOT](figures/decoerenza.svg)

Con l'evoluzione controllata come accoppiamento, lo stato è `α|0⟩|0⟩ + β|1⟩ U|0⟩`. `partial_coherence` dice che la coerenza del sistema è `α β̄ · conj(⟨0|U|0⟩)` nel libero, con `⟨0|U|0⟩ = c − i s nz`; `partial_diagonal` che la diagonale resta la coppia di Born modulo `(gC, gN)`. Lungo x, per `ψ = Φ|0⟩` nel punto, `partial_reading` dà coerenza `(12/25 i)·c` e purezza `337/625 + (288/625)·c²`: `1`, `11017/15625` e `337/625` in `c = 1`, `3/5`, `0`. La misura ha gradi; quella perfetta è un punto.

![Misura parziale: l'accoppiamento viene da un'Hamiltoniana](figures/misura-parziale.svg)

Leggere il puntatore. `condition k` proietta l'apparato su `|k⟩` e restituisce lo stato non normalizzato del sistema; `condition_norm` dà la sua norma per ogni `Quad`. `luders` dice che dopo `CNOT` su `|ψ⟩ ⊗ |0⟩` le due letture lasciano `(α, 0)` e `(0, β)`, con norme `bornPair ψ`: la regola di aggiornamento è un teorema. `repeatable` accoppia un secondo apparato allo stato condizionato: legge lo stesso esito con lo stesso peso, e l'altro con peso zero. `point_luders` e `point_repeatable` sono i valori nel punto, `3/5|0⟩` e `−4/5 i|1⟩` con pesi `9/25` e `16/25`.

Due apparati. `cnot01` agisce dal bit alto al bit medio, `cnot02` dal bit alto al bit basso. `two_pointers` dà `α|000⟩ + β|111⟩` su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩`. `observers_agree` dice che i pesi delle celle 1–6, dove i due puntatori differiscono, sono il polinomio zero. `order_irrelevant` scambia l'ordine dei due `CNOT`. Le versioni `_right` passano per `tensor_assoc`.

![Due apparati sullo stesso sistema](figures/osservatori.svg)

L'amico di Wigner. `cnot12` agisce dal bit medio al bit basso: Wigner legge l'amico. `chain_pointers` e `chain_is_fanout` danno, su `|ψ⟩ ⊗ |0⟩ ⊗ |0⟩`, lo stesso stato di `two_pointers`; `chain_agree` è l'accordo. `reduceSystem` è la traccia parziale su amico e Wigner, e `reduceSystem_product` la riporta a `|ψ⟩⟨ψ|` su un prodotto. `friend_undone`: `cnot01` due volte restituisce lo stato e la coerenza `α β̄`. `copy_irreversible`: dopo `cnot12` lo stesso `cnot01` lascia `α|000⟩ + β|101⟩`, i due termini fuori diagonale sono il polinomio zero e la diagonale è `bornPair ψ`; `wigner_keeps_record` dice che Wigner legge ancora quella coppia. Nel punto, `point_undone` dà coerenza `12/25 i` e purezza `1`, `point_copied` coerenza `0`, purezza `337/625` e pesi `9/25`, `16/25`. `no_signalling_wigner` e `no_signalling_friend` valgono per ogni `v : Oct`: il marginale del sistema è una somma di due norme di un qubit. Tutto sta nel libero tranne il no-signalling, in `(gC, gN)`. Che cosa questo dica sulla misura è `researches/misura.md`.

![L'amico di Wigner: disfare l'amico restituisce la coerenza prima della copia, non dopo](figures/wigner.svg)

Un unitario locale sull'apparato non cambia i pesi del sistema, per ogni stato di due qubit. `no_signalling_any_0` e `no_signalling_any_1` confrontano `marginalLeft (applyIU evolution v)` con `marginalLeft v` per ogni `v : Quad`. L'argomento è una riga: `I ⊗ U` agisce su ciascun blocco `(a₀, a₁)` e `(a₂, a₃)` come `U` su un qubit, quindi ogni componente della differenza è `‖Uγ‖² − ‖γ‖²`, che `literal_evolution_norm` mette in `(gC, gN)`. `no_signalling_gen_0` e `no_signalling_gen_1` sono il caso `genericQuad`, le cui quattro celle usano gli otto esponenti delle ampiezze di `Mono`. `no_signalling_0` e `no_signalling_1` sono il caso `CNOT(|ψ⟩ ⊗ |0⟩)`.

Il certificato Python fa lo stesso conto su uno stato di due qubit generico, otto reali di ampiezza più `c`, `s`, `n`, e cita `no_signalling_gen_0` e `no_signalling_gen_1`.

![Un unitario sull'apparato: i pesi del sistema restano, quelli dell'apparato cambiano](figures/segnale.svg)

La ripartizione è questa. Nel libero stanno `CNOT`, il determinante, la decoerenza, `pointer_born` e l'accordo dei due apparati. In `(gC, gN)` sta il no-signalling, con i cofattori di `δ`. `purity_sphere` usa `gA`. Il certificato Python esegue `CNOT`, il determinante, la decoerenza, `pointer_born`, la purezza nel punto, i due osservatori e il no-signalling sullo stato generico. `reduceLeft_diag`, `reduce_product`, `purity_before` e `purity_sphere` sono solo in Lean.

Questo non dice quale esito avviene, né perché la base sia quella computazionale: la base è scelta da `CNOT`. Dice che, dentro il modello, i pesi di Born sono ciò che un sottosistema registra, che due registrazioni coincidono, e che un unitario locale sull'apparato non li cambia.

L'argomento, i vicoli ciechi e i tre candidati per il passo successivo sono in [`researches/osservatore.md`](../researches/osservatore.md).

Il monomio di Lean ha diciotto esponenti con nome: `c s nx ny nz` per la legge, otto per le ampiezze di due qubit, `c2 s2` per un secondo passo di tempo, `mx my mz` per un secondo asse. La divisione legge solo `c` e `nx`. `evalAt` legge i cinque della legge, `evalAt2` anche `c2 s2`, `evalAt3` anche `mx my mz`. Perché restano campi con nome e non un parametro è `researches/monomio.md`.

## 8. Fuori da questa nota

Fuori dalla 1.0 (`plans/roadmap.md`): un secondo universo fisico, la meccanica classica, una libreria di basi generali, Mathlib, e la verifica del sorgente Python dentro Lean. Il tempo continuo è la tappa M3. I limiti del nucleo (l'esito singolo, l'origine della regola di Born, lo spazio, i campi, la gravità) sono in `researches/misura.md`, `researches/born.md` e `researches/distanza.md`.
