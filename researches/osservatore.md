# L'osservatore interno

Argomento di `Universe.Observer.pointer_born`. I nomi in corpo di testo sono lemmi di Lean 4.34.1. La ripartizione delle identità è `papers/qubit.md`, sezione 7. L'indice è il README. Righe e conteggi del codice sono al commit `abae267`.

## Enunciato

`pointer_born` è `pointer_diag` applicato a `Φ|ψ⟩`. Il calcolo nuovo è quello di `pointer_diag`.

```lean
theorem pointer_born (ψ : Pair) :
    polySame (reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))).a01 [] ∧
      polySame (reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))).a10 [] ∧
        pairSame ⟨(reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))).a00,
            (reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))).a11⟩
          (bornPair (applyMat evolution ψ)) :=
  pointer_diag (applyMat evolution ψ)
```

`Obs` era la misura proiettiva nella base computazionale, passata al nucleo da fuori. Qui è la diagonale dello stato ridotto dell'apparato, calcolata con `CNOT`, la traccia parziale e `columnBorn`.

## Perché il libero basta

`applyCNOT` scambia `|10⟩` e `|11⟩`. `cnot_ket0` riscrive `|ψ⟩ ⊗ |0⟩` in `α|00⟩ + β|11⟩`: le celle 1 e 2 sono la lista vuota. In `reduceLeft` la coerenza è `α · conj(0)` accanto a `0 · conj(β)`. `pmul_nil` annulla entrambi. La diagonale resta `columnBorn α` e `columnBorn β`. È `decoherence` in `Universe/Observer.lean`. Un polinomio zero di lista vuota non è un resto di `reduce`, e non chiede cofattori.

`reduceRight` sullo stesso stato legge le stesse due celle. I pesi sono quelli di `Φ|ψ⟩`, normalizzati o no. La somma uguale a `1` è un altro enunciato: su `Φ|0⟩` è `ground_prob_sum`.

Due apparati partono da `ket0`. `two_pointers` lascia `α` in cella 0 e `β` in cella 7. `observers_agree` applica `bornOct`: sulle celle 1–6 il peso è `columnBorn` della lista vuota. L'accordo è il supporto di `α|000⟩ + β|111⟩`. `order_irrelevant` è la stessa ottupla. `tensor_assoc` la sposta sulla parentesizzazione destra, per uguaglianza di liste.

`product_det` non ha aperto il rischio del piano. `polySame_mul_comm` e `polySame_assoc_comm` c'erano già. Il determinante di un prodotto è zero in una dozzina di righe.

## Che cosa «derivato» nomina

Il teorema dice che un sottosistema, l'apparato in `|0⟩` dopo questo `CNOT`, registra la coppia `bornPair (Φ|ψ⟩)`. La coppia resta due polinomi. Non è un esito scelto fra i due, e non è un ramo cancellato.

La base è la permutazione scritta in `applyCNOT`. `evolution` è `c I − i s H` su un solo qubit, e non produce quella permutazione. Nessun lemma ricava la base da `Φ`.

## Chi paga

Nel libero stanno `CNOT`, il determinante, `decoherence`, `pointer_born`, `purity_after` e l'accordo dei due apparati. `cnot_norm` scambia gli ultimi due `columnBorn` con `Gauss.add_comm`. `purity_after` è `|α|⁴ + |β|⁴`.

In `(gC, gN)` stanno `no_signalling_0` e `no_signalling_1`. `I ⊗ U` moltiplica la cella 0 per la prima colonna di `U` e la cella 3 per la seconda. L'appartenenza all'ideale arriva da `δ`.

`gA` paga `purity_sphere`. `one_sub_square` scrive `1 − n²` con cofattori vuoti su `gC` e su `gN`, e con cofattore `−(n + 1)` su `gA`. `n − 1` è `gA` per `normPair_generic`. `reduce` non vede questo difetto: sbuccia solo `c²` e `nx²`, e `inIdeal3` non estende `inIdeal`.

## Vicoli ciechi

`point_prob0` valuta un modulo quadro, `9/25`. Il determinante nel punto è un prodotto, `−12/25 i`. `point_entangled` espande `quadDet` con quattro `mulMono_single` e con `specPoly keepX`, e chiude in `grind`. `eval_polySame`, `eval_pmul` ed `eval_conj` stanno in `Universe/Evaluation.lean`, 182 righe, e sono posteriori: li usa `point_purity`. Il teorema della fase 1 resta com'è.

`evolution_unitary` è `U†U`, dunque `conj(z) · z`. `columnBorn` è `z · conj(z)`. La citazione diretta non chiude il marginale. La prima prova trasportava `evolution_unitary` sull'ordine `z · conj(z)` con due lemmi di colonna. Era un giro lungo: il marginale di un blocco è già `‖Uγ‖²`, e `literal_evolution_norm` lo chiude per ogni coppia di ampiezze (vedi «Dopo la nota»).

Lo stato di due qubit con quattro ampiezze libere non entra in `Mono`. Il tetto della fase 4 era circa 300 righe, oppure un campo nuovo. `no_signalling_0` e `no_signalling_1` restano entro quel tetto, perché `cnot_ket0` svuota le celle 1 e 2: l'apparato è la costante `1` e la costante `0`. Il certificato Python fa lo stesso conto su tredici indeterminate, `(c, s, nx, ny, nz, a0r, …, a3i)`. Otto reali di ampiezza non sono i quattro esponenti `ar ai br bi`.

## Tre candidati

Base preferita dall'interazione, al posto di un `CNOT` fissato. Si respinge come prossimo teorema Lean. `decoherence` è già la diagonalità in questa base, e la prova è `cnot_ket0` con `pmul_nil`. Una seconda base è un secondo unitario. Nei nove esponenti l'unico unitario è `evolution`, e `c`, `s`, `n` sono la legge. Una libreria di basi resta fuori da `papers/qubit.md`, sezione 8. Dirlo in Lean costa quanto il candidato seguente. In Python basta un anello fresco, come gli otto reali di `‖CNOT v‖²`: la riga nomina ancora la base.

Hamiltoniano generico di due qubit, con `Mono` reso parametrico. Si conferma, ed è l'ostacolo anche del candidato precedente. `Universe/Quotient.lean` ha 1849 righe. `Mono` ha nove campi `Nat`, righe 26–36: `c s nx ny nz ar ai br bi`. La larghezza è elencata in `Mono.mul`, `subExp`, `subExp_mul` e `mul_subExp` (righe 42–92), nei nove bullet di `shiftC_cSq` e di `shiftNx_nxSq` (righe 193–203 e 479–489) e in dieci literal a nove componenti: `Mono.one`, i cinque quadrati della legge, i quattro delle ampiezze. `shiftC` e `shiftNx` usano `{m with …}`, e un campo spettatore si conserva. Le 18 occorrenze di `ext <;>` non crescono di una riga per campo. Il peso è `3^c · 2^nx` (riga 211). Da `termWeight` a `reduceC_sound` (riga 1836) l'argomento vede solo quei due gradi.

Quattro esponenti spettatori in più, una seconda coppia di ampiezze, modificano l'interfaccia: qualche decina di righe, non le 1849. `monoVal` e `evalAt` (`Universe/Epistemology.lean`, righe 1007–1014) moltiplicano cinque razionali, `c s nx ny nz`, e ignorano già `ar ai br bi`. Le 16 dichiarazioni di `Universe/Evaluation.lean` stanno su quella firma. Un esponente che non si valuta non le tocca. Un esponente che si valuta le tocca tutte.

Le 73 occorrenze di `.c` e le 61 di `.nx` non sono tutte interfaccia. 62 e 51 stanno nel corpo della divisione, fra la riga 211 e la riga 1836. 48 righe contengono `by decide`. Vi si mescolano confronti di monomi (`sSq ≠ cSq`), gradi concreti (`¬ 2 ≤ m.c`) e l'aritmetica del peso (`(2 : Nat) < 9`). Un campo spettatore non le muove: `c` e `nx` restano `Nat`, e il peso non nomina gli altri campi. I confronti di monomi si muovono se `Mono` perde il `DecidableEq` derivato, cioè se la lunghezza diventa un tipo astratto.

Una hermitiana su `ℂ² ⊗ ℂ²` ha 16 reali e non quadra a `I`. `Universe.Qubit.expCoeff_hamiltonian` usa il collasso di `Universe/Series.lean` (146 righe): i coefficienti formali `cosCoeff` e `sinCoeff`, il fattoriale cancellato, l'ipotesi `a² = 1`. `Universe/Qubit.lean` è 921 righe per l'unico `H = n·σ` che soddisfa quell'ipotesi. Senza il quadrato la serie non si chiude e non c'è un `c` da sbucciare. Un terzo quadrato da sbucciare, accanto a `c²` e `nx²`, è una divisione duplicata, come `gN` accanto a `gC`. L'ostacolo è questo. Allargare `Mono` è il passo necessario, e non è il passo che chiude l'hamiltoniano.

`c` e `s` come `cos φ` e `sin φ` reali, senza Mathlib. Non vale il costo. Il legame già dimostrato è la serie formale. `evalAt` sostituisce razionali. L'unico punto del certificato è `c = 3/5`, `s = 4/5`: `9/25` e `16/25` sono i quadrati di quelle frazioni, e `δ` vale zero per `point_gC`, `point_gN` e `point_unitary`. Un coseno con resto non sposta nessuna appartenenza a un ideale. Mathlib resta fuori dalle regole. Le 182 righe di `Evaluation.lean` coprono le sostituzioni razionali che il certificato usa.

## Dopo la nota

Il monomio è passato da nove a tredici esponenti (`plans/parametric-mono.md`, fase 1), con quattro spettatori che la divisione non legge. Lo stato generico di due qubit è entrato in Lean, ma la prova non ne ha avuto bisogno: `no_signalling_any_0` e `no_signalling_any_1` valgono per ogni `v : Quad`, e sono `literal_evolution_norm` applicato ai due blocchi del sistema. La prova della fase 4, circa novanta righe con `born_column_defect` e i due lemmi di colonna, era un caso particolare dello stesso argomento ed è stata tolta: `no_signalling_0` e `no_signalling_1` ne sono ora corollari di una riga.

Il vicolo cieco non era il monomio. Era cercare la prova sulla forma `α|00⟩ + β|11⟩` invece che sul blocco.

## Fuori da questo argomento

`gA` entra solo in `purity_sphere`. `reduce` sbuccia ancora solo `c²` e `nx²`. Restano fuori anche un secondo universo fisico, il limite continuo, la meccanica classica, una libreria di basi generali, Mathlib, e la verifica del sorgente Python dentro Lean.

## Verifica

`lake build` sulla libreria `Universe`. `python -m universe` stampa 42 righe, chiude con `42/42` ed esce 0.
