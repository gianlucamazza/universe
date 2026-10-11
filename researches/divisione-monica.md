# Divisione monica di `reduce`

Argomento di `Universe.Dynamics.reduce_complete`. I nomi in corpo di testo sono lemmi di Lean 4.34.1. La ripartizione delle identità è `papers/qubit.md`. L'indice è il README.

## Enunciato

```lean
theorem reduce_complete (p : Poly) (h : inIdeal p) (t : Mono) :
    coeffOf (reduce p).rem t = 0
```

`inIdeal` è l'esistenza di due cofattori per `(gC, gN)`. Il resto può essere una lista non vuota i cui coefficienti si cancellano: l'enunciato è su `coeffOf`, come `reduce_gC_rem`.

## Perché questa divisione

`gC` è monico di grado 2 in `c`. `gN` è monico di grado 2 in `nx`. Le due variabili sono disgiunte, quindi ciascuna si divide da sola. Una libreria di basi generali resta fuori dalla nota. La divisione monica evita di dimostrare che `ℚ(i)` è un campo.

## Passi

`reduceC` sbuccia solo `c²`. Il peso di un polinomio è `Σ 3^{m.c}`. Un passo sostituisce `c²` e porta il contributo `3^c` in `2 · 3^{c−2}`: `2 < 9`, quindi il peso scende. `reduceC_sound` ricostruisce i coefficienti come `cAssemble`, resto più un multiplo di `gC`. `reduceC_small` dice che il resto è `cListSmall`.

Se `f · gC` è `cSmall`, ogni fetta `sliceC k f` ha coefficienti zero. L'induzione scende da `cBound f`. Sopra il bound la fetta è la lista vuota, `sliceC_above`. La ricorrenza è `coeff_slice_mul_gC`: il coefficiente della fetta di grado `k + 2` del prodotto è quello della fetta `k` di `f` più quello della fetta `k + 2` moltiplicata per `gC0 = s² − 1`. La fetta alta, già nulla, dà un prodotto nullo tramite `coeff_mul_congr_left` contro la lista vuota. `mul_gC_low` ricostruisce il polinomio con `coeff_via_sliceC`.

Lo stesso schema, duplicato e non astratto, vale per `gN`, `sliceNx` e `gN0 = ny² + nz² − 1`. I lemmi sono `sliceNx_of_mul_gN` e `mul_gN_low`.

Sia `r` normale e `r = fc · gC + fn · gN` sui coefficienti. `reduceC fn` scrive `fn` come `ρ ++ q · gC` con `ρ` di grado in `c` minore di 2. Allora `r` e `ρ · gN` differiscono per un multiplo di `gC`. Entrambi sono `cSmall`: `r` perché `normal_cListSmall`, il prodotto perché `cListSmall_mul` e `listCFree_gN`. `mul_gC_low` annulla la differenza, quindi `r` e `ρ · gN` hanno gli stessi coefficienti. `r` è `nxSmall`, quindi `mul_gN_low` annulla `ρ` e, di nuovo per `coeff_mul_congr_left`, annulla il prodotto. Dunque ogni coefficiente di `r` è zero. È `normal_ideal_zero`.

`reduce_normal` e `reduce_sound`, insieme a `inIdeal`, scrivono `(reduce p).rem` come un resto normale dell'ideale. `polySame_dot_sub_left` sposta i cofattori di `reduce` su quelli dell'appartenenza. Questo è `reduce_complete`.

Il motore delle fette, `reduceC` e le ricorrenze stanno in `Universe.Quotient`. L'annullamento del prodotto e l'ideale stanno in `Universe.Dynamics`, perché `coeff_mul_congr_left` usa `support` e `listContrib`.

## Testimone e cofattori

I cofattori non sono unici. `gN · gC + (−gC) · gN` ha tutti i coefficienti zero, con cofattori non banali. Il teorema azzera un resto normale. Non sceglie un cofattore.

`reduce_gC_rem` e `reduce_gN_rem` restano il calcolo diretto sui due generatori.

`python -m universe` stampa 39 righe. Una riga è dimostrata quando il resto è zero e l'espansione libera dei cofattori ricostruisce il polinomio. Quel testimone eseguibile e `reduce_complete` si citano. Il teorema è su `Universe.Quotient.reduce`.

## Fuori da questo argomento

`gA` e `inIdeal3` non entrano in `reduce`. Restano fuori anche un secondo universo fisico, il limite continuo, la meccanica classica, una libreria di basi generali, Mathlib, e la verifica del sorgente Python dentro Lean.

## Verifica

`lake build` sulla libreria `Universe`. `python -m universe` stampa `39/39` ed esce 0.
