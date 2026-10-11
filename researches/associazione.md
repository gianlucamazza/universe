# Associazione di tre qubit

Argomento di `Universe.Composition.tensor_assoc`. I nomi in corpo di testo sono lemmi di Lean 4.34.1. La ripartizione delle identità è `papers/qubit.md`. L'indice è il README.

## Enunciato

Due descrizioni sono lo stesso universo quando un isomorfismo commuta con `Φ` e con `Obs`. Qui le due descrizioni sono le parentesizzazioni di tre qubit.

```lean
theorem tensor_assoc (ψ φ χ : Pair) :
    tensorLeft (tensorPair ψ φ) χ = tensorRight ψ (tensorPair φ χ)
```

`tensor_assoc_ui` è `(U ⊗ I ⊗ I)((ψ ⊗ φ) ⊗ χ) = ((Uψ) ⊗ φ) ⊗ χ`. `tensor_assoc_ui_right` è la stessa uguaglianza sulla parentesizzazione destra. `tensor_assoc_obs` identifica i moduli quadri delle otto celle.

Associazione e poi `U` sul primo fattore è la stessa lista di `U` e poi associazione.

![Le due parentesizzazioni e U sul primo fattore](../papers/figures/quadrato.svg)

`tensor_assoc_obs` identifica `z · conj(z)` su ogni cella dei due stati prima di `U`. I due stati dopo `U` hanno gli stessi pesi perché quegli stati sono uguali.

## Codifica

L'indice di `|i⟩ ⊗ |j⟩ ⊗ |k⟩` è `4 · i + 2 · j + k`. Le celle `0` … `7` sono i bit `(i, j, k)` in ordine lessicografico. `tensorLeft` moltiplica una quad per il terzo fattore: la cella `2 · q + k`. `tensorRight` moltiplica il primo fattore per una quad: la cella `4 · i + q`. Su uno stato prodotto le due liste coincidono per `pmul_assoc`. È un'uguaglianza di liste, nell'anello libero.

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

`applyUII` usa la prima riga di `U` sulle celle `0`–`3` e la seconda sulle celle `4`–`7`.

Tre copie di `Φ|0⟩` nel punto `c = 3/5`, `s = 4/5`, `n = eₓ` danno un'altezza a ogni cella. Il peso è `(9/25)` per ogni zero e `(16/25)` per ogni uno. `point_prob0` e `point_prob1` sono i fattori. Il certificato valuta il triplo tensore, sulle due parentesizzazioni, e stampa le otto frazioni. La somma è `1`. La figura è `papers/figures/celle.svg`.

![Otto celle di tre copie di Φ|0⟩](../papers/figures/celle.svg)

`tensorIndex_assoc_qubit` è `Universe.Ontology.tensorIndexAssoc` con dimensioni `2` e `2`. Il passo intermedio scambia `2 * i` con `i * 2`, poi cita quel teorema sui naturali.

`assoc_row` è la riga

```text
u₀ · ((x₀ · y) · z) + u₁ · ((x₁ · y) · z) = ((u₀ · x₀ + u₁ · x₁) · y) · z.
```

`pmul_assoc` tira fuori i prodotti. `pmul_append_left` tira fuori la somma, prima dal prodotto esterno e poi da quello interno. `applyUII` usa questa riga sul bit alto, a blocchi di quattro. Le otto celle di `tensor_assoc_ui` sono `assoc_row` con `(y, z)` che percorre `φ` e `χ`, e con la seconda metà della matrice sulle celle `4` … `7`. La parentesizzazione destra segue per riscrittura di `tensor_assoc`.

`bornOct` applica `columnBorn`, cioè `z · conj(z)`, a ogni cella. `tensor_assoc_obs` riscrive `tensor_assoc`.

## Testimone

`python -m universe` stampa 57 righe. La riga di associatività resta una sola. Gli indici stanno sull'anello `(i, j, k, nb, nc)`: è l'identità polinomiale di `tensor_index`, dunque `tensorIndexAssoc` sui naturali. Ampiezze e `(U ⊗ I ⊗ I)` stanno sull'anello `(u00, u01, u10, u11, a0, a1, b0, b1, c0, c1)`. Le tre scritture `(U ⊗ I) ⊗ I`, `U ⊗ (I ⊗ I)` e `U ⊗ I₄` danno lo stesso stato di `U` applicato al primo fattore e poi composto. I moduli quadri delle due parentesizzazioni coincidono, e coincidono anche dopo `Φ`, perché gli stati coincidono. Il dettaglio cita `tensor_index`, `Universe.Composition.tensor_assoc`, `tensor_assoc_ui` e `tensor_assoc_obs`.

## Fuori da questo argomento

`gA` e `inIdeal` restano com'erano. `reduce` sbuccia ancora solo `c²` e `nx²`. Restano fuori anche un secondo universo fisico, il limite continuo, la meccanica classica, una libreria di basi generali, Mathlib, e la verifica del sorgente Python dentro Lean.

## Verifica

`lake build` sulla libreria `Universe`. `python -m universe` stampa `57/57` ed esce 0.
