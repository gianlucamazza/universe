# Il monomio come parametro

Argomento della fase 3 di `plans/parametric-mono.md`. I nomi in corpo di testo sono lemmi di Lean 4.34.1. Il codice è al commit `36d4cc2`. La fase 1 è `66984b1`.

## Domanda

Gli esponenti delle ampiezze possono diventare un parametro, così che tre qubit, sedici reali, non chiedano un'altra modifica di `Mono.mul`, di `subExp` e delle prove `ext`? Le forme provate sono `amp : List Nat`, `amp : Fin n → Nat`, `amp : Vector Nat ampWidth`, e `Mono (w : Nat)`.

## Quanto costa lasciarli espliciti

La fase 1 ha sostituito i bullet per campo con `ext <;> simp` e con `omega`, e i letterali con `{Mono.one with …}`. Il commit toglie 39 righe nette e dice che il prossimo allargamento lascia le prove com'erano.

Sonda, poi tolta. Otto campi `a4r a4i a5r a5i a6r a6i a7r a7i` dopo `a3i`: i sedici reali di tre qubit, otto in più degli otto già presenti accanto a `c s nx ny nz`. Il diff è solo `Universe/Quotient.lean`, 30 righe aggiunte e 2 riscritte. Il file passa da 1817 a 1845 righe. I quattro siti sono la `structure` (righe 27–41), `Mono.one` (45–58), `Mono.mul` (60–73) e `subExp` (77–85). `lake build` chiude. `Dynamics`, `Qubit`, `Epistemology`, `Evaluation`, `Composition` e `Observer` compilano su quella sonda senza una riga propria.

Restano gli script di prima. Quattro in `Dynamics.lean`: `Mono.mul_comm`, `Mono.mul_assoc`, `Mono.one_mul`, `Mono.mul_one`. Tredici in `Quotient.lean` passano `Mono.mul` a `simp`. `Mono.mul_right_cancel` (riga 1085) e `mono_mul_left_cancel` usano `Mono.mk.injEq` con `Nat.add_right_cancel_iff` e `Nat.add_left_cancel_iff`. Ventiquattro `by decide` confrontano monomi chiusi, da `sSq ≠ cSq` (riga 340) a `Mono.one ≠ nzSq` (riga 905). Stanno fra `termWeight` (riga 211) e `reduceC_sound` (riga 1802).

Le dodici ampiezze con nome restano `{Mono.one with campo := n}`: `ar1`, `ai1`, `br1`, `bi1`, `a2r1`, `a2i1`, `a3r1`, `a3i1`, `arSq`, `aiSq`, `brSq`, `biSq`. Un reale nuovo è una riga nel punto in cui lo si nomina, e quattro righe nei quattro siti sopra.

## Lista

`structure Mono where law : LawExp; amp : List Nat`, con `DecidableEq` derivato. Compilato con Lean 4.34.1, fuori dalla libreria.

`decide` chiude `⟨legge zero, []⟩ ≠ ⟨legge zero, [0]⟩`. Un `coeff` sulla lista `[(1, [])]` vale 1 sul primo monomio e 0 sul secondo. L'esponente assente è lo zero del monomio. `List.zipWith (· + ·) [1] [1, 0]` valuta `[2]`: l'esponente in coda sparisce. `coeffOf` identifica i termini con `e = m`, l'uguaglianza derivata. Una forma canonica, padding fisso oppure zeri in coda cancellati, è un'altra relazione.

## Funzione su un Fin

`amp : Fin 8 → Nat`. `deriving DecidableEq` fallisce: non sintetizza `Decidable (a = b)`. I ventiquattro `by decide` del tratto della divisione confrontano monomi. Senza l'istanza quei passi si fermano, e la prova legge gli esponenti delle ampiezze per decidere `sSq ≠ cSq`.

## Vettore a larghezza fissa

`ampWidth := 8`, `amp : Vector Nat ampWidth`, `@[ext]`, `DecidableEq` derivato. Il tipo si chiama ancora `Mono`. `by decide` chiude `Mono.one ≠ cSq`.

Lo script di `Mono.one_mul`, `ext <;> simp [Mono.mul, Nat.zero_add]`, lascia gli obiettivi `one.c = 0` e `one.amp[i] = 0`. `Nat.zero_add` non si applica. Gli stessi obiettivi si chiudono se ogni proiezione ha un lemma `@[simp]`: con quei lemmi, `Mono.one_mul` e `Mono.mul_comm` compilano. `mul_subExp` usa `simp only [Mono.mul]` e poi `omega`. `simp only` ignora i lemmi `@[simp]`. Sul ramo negativo di `subExp`, la condizione vettoriale è `∀ i, m.amp[i] ≤ t.amp[i]`, e `omega` risponde che non vede vincoli lineari.

`Mono.mul_right_cancel` è `Mono.ext_iff`, poi `simp only [Mono.mul, Mono.mk.injEq, Nat.add_right_cancel_iff]`. Dopo `simp`, l'ipotesi ha tipo

```text
b.c = c.c ∧ … ∧ b.amp + a.amp = c.amp + a.amp
```

e il passo chiede `b.amp = c.amp`. `Nat.add_right_cancel_iff` cancella i `Nat` e si ferma sul vettore. `factor_cSq` (riga 1278) e `factor_nxSq` (riga 1293) chiamano questo lemma. Stanno nel tratto che arriva a `reduceC_sound`.

La cancellazione sulle componenti si scrive a parte. `Vector.add_right_cancel_iff` sono dodici righe: `Vector.ext`, la proiezione, `Nat.add_right_cancel`. `mul_right_cancel` deve nominarla. È un lemma sulla somma delle ampiezze, usato dalla divisione.

## Indice nel tipo

`structure Mono (w : Nat)` rende `Poly` una famiglia `Poly w`. `coeffOf_nil` oggi è `coeffOf [] m = 0` per `m : Mono`. Con l'indice l'enunciato quantifica su `w`. L'accettazione della fase 1 chiede lo stesso nome e lo stesso enunciato. Tre qubit sono un altro tipo: ogni teorema che dice `Mono` o `Poly` cambia.

## Conto

Otto reali in più, campi espliciti: 28 righe nette, un file, le prove restano, la libreria compila. La lista sdoppia i coefficienti di uno stesso monomio. La funzione su `Fin` toglie `DecidableEq` ai `decide` della divisione. L'indice nel tipo cambia gli enunciati. Il vettore tiene `decide` ed `ext`, chiede lemmi `@[simp]` sulle proiezioni, e chiede una cancellazione sul vettore che `factor_cSq` e `factor_nxSq` usano. `omega` non chiude `subExp`. Le dodici ampiezze con nome diventano indici. Il prossimo qubit, con i campi espliciti, è di nuovo una manciata di nomi negli stessi quattro siti.

La fase 3 si ferma. `Quotient.lean` resta a 1817 righe.

Dopo la nota. Il problema che questa nota misurava, un qubit in più costa `2ⁿ⁺¹` reali con nome, è chiuso senza un monomio parametrico (`plans/n-qubits.md`). Uno stato di `n` qubit è un albero di polinomi, `Universe.Qubits.QState`, e i teoremi valgono per ogni stato, come già `no_signalling_any_0` per ogni `Quad`: le ampiezze non sono indeterminate di `Mono`, quindi `Mono` non cresce.

## Fuori da questo argomento

`gA` resta fuori da `reduce`. `monoVal` e `evalAt` restano su `c s nx ny nz`. Il certificato è il Python, e questa nota non lo tocca. `README.md`, `papers/` e la fase 4 non sono questo testo.

## Verifica

`lake build` sulla sonda a ventuno esponenti, poi `git checkout` del file: il sorgente Lean torna a `36d4cc2`. I file della prova (`Lista`, `FinFun`, `VectorBreak`, `VectorSimp`, `VectorCancel`) sono compilati fuori dal repository e non entrano nella libreria. Nessun `sorry`.
