# Plan: every number of qubits

Executor: `grok` (`grok-4.7`). Orchestrator and reviewer: Claude.
Status: in progress. Milestone M2 of `plans/roadmap.md`, release `v0.6.0`.

| Phase | State   | Goal                                                                    |
| ----- | ------- | ----------------------------------------------------------------------- |
| 0     | done    | spike: `n`-qubit states, a gate on any qubit, the norm is kept          |
| 1     | done    | no-signalling between any two qubits, for every `n`                     |
| 2     | planned | gates on different qubits commute; the state of one qubit               |
| 3     | planned | `n` observers on one system: `α\|0…0⟩ + β\|1…1⟩`, and every pair agrees |
| 4     | planned | the `Quad` and `Oct` theorems are the cases `n = 2` and `n = 3`         |
| 5     | planned | docs, figure, release                                                   |

## 1. Why

Criterion 1 of `plans/roadmap.md`: the structural theorems must hold for `n` qubits, for
every `n`. Today they hold for `Pair`, `Quad` and `Oct` separately (`Universe/Composition.lean`,
`Universe/Observer.lean`), and each new size has cost a new structure and new proofs.

`researches/monomio.md` measured why a generic state does not scale: `n` qubits need `2ⁿ⁺¹`
named reals in `Mono`. The way around it is already in the code. `no_signalling_any_0` is
stated for every `v : Quad`, and it is `literal_evolution_norm` on each block: no generic
monomials. This plan states every theorem for every state, so `Mono` does not grow.

Lean core has no sums over finite sets, and this repository has no Mathlib. The state is
therefore a perfect binary tree, and every proof is an induction on `n`:

```lean
inductive QState : Nat → Type where
  | leaf : Poly → QState 0
  | node : QState n → QState n → QState (n + 1)
```

`node l r` splits on the first qubit: `l` is the branch where it reads `0`, `r` where it reads
`1`. The cell order is the one of `Quad` and `Oct` (`2i + k`, `4i + 2j + k`).

Phase 0 note: the spike closed in 134 lines. Its review moved the law out of `Scalars`
(`Law`, `law_ring` in `universe/ring.py`), so `dynamics.py` no longer asks for amplitudes it
does not read, and created `universe/qubits.py` (`generic_state`, `on_qubit`): the three copies
of the same fresh-ring construction in `universe/observer.py` and in the tests are gone.

## 2. Ground rules

Section 2 of `plans/observer-inside.md` and of `plans/no-outside.md` apply in full. In
addition:

- Lean in `Universe/Qubits.lean`. Python in `universe/qubits.py` (`generic_state`, `on_qubit`),
  reusing `universe/ontology.py` and `universe/observer.py` (`reduced`, `marginal`).
- No workaround and no technical debt: no duplicated construction, no helper that returns
  something other than what its name says, no doc left behind. Each phase adds its
  certificate lines and their `lean_map` keys.
- No new `Mono` field. Every theorem quantifies over every state (`QState n`) and every `n`.
- Reuse: `literal_evolution_norm`, `inIdeal_append` and the `inIdeal` congruences,
  `columnBorn`, `matMul`, `evolution`, `polySame` lemmas.
- Python checks the same facts on generic states for `n = 1, 2, 3, 4` (`4` means sixteen
  amplitudes, thirty-two reals): a theorem for every `n` is a Lean fact; Python is the
  witness on small cases.

## 3. Phases

### Phase 0 (spike): the norm is kept by a gate on any qubit

1. `QState`, `normQ : QState n → Poly` (sum of `columnBorn` over the leaves),
   `applyAt : Fin n → Mat → QState n → QState n` (on qubit `0` of `node l r`, the matrix
   mixes `l` and `r` leaf by leaf; on qubit `k + 1`, it acts inside both children).
2. `theorem norm_applyAt (k : Fin n) (v : QState n)`: `normQ (applyAt k evolution v) − normQ v`
   is `inIdeal`.

Go/no-go: at most ~300 lines. If it does not close, write `researches/qubits.md` with the
design tried and where it broke, and stop the plan.

### Phase 1: no-signalling between any two qubits

1. `marginalAt : Fin n → QState n → Pair`, the Born pair of one qubit.
2. `theorem no_signalling_at (a b : Fin n) (h : a ≠ b) (v : QState n)`: both components of
   `marginalAt a (applyAt b evolution v) − marginalAt a v` are `inIdeal`.
3. Python: generic states, `n = 2, 3, 4`, every pair `a ≠ b`.

### Phase 2: commuting gates, and the state of one qubit

1. `theorem applyAt_comm (h : a ≠ b)`: gates on different qubits commute, leaf by leaf up to
   `polySame`, for every pair of matrices.
2. `reduceAt : Fin n → QState n → Mat`, the partial trace onto one qubit; `reduceAt_diag`:
   its diagonal is `marginalAt`; `reduceAt_product`: on a product state it is `‖rest‖² |ψ⟩⟨ψ|`.
3. Python: the same, `n ≤ 4`.

### Phase 3: `n` observers on one system

1. `cnotFrom0 : Fin n → QState n → QState n`, a `CNOT` from qubit `0` to qubit `k`.
   `fanout n`: all of them, on `|ψ⟩ ⊗ |0…0⟩`.
2. `theorem fanout_ghz`: the result is `α|0…0⟩ + β|1…1⟩`: every other leaf is the zero
   polynomial.
3. `theorem fanout_agree`: for every pair of observers, the cells where they differ have Born
   weight zero; `theorem fanout_decoherence`: for `n ≥ 2` the system's reduced state is
   diagonal with `bornPair ψ`.
4. Python: `n ≤ 5` on a generic `ψ`.

### Phase 4: the old structures are cases

Maps `toQuad`/`ofQuad`, `toOct`/`ofOct`, and lemmas that `applyAt` is `applyUI`, `applyIU`,
`applyUII`, `applyIUI`, `applyIIU` under them. Then every `Quad` and `Oct` theorem that the
`n`-qubit theorems cover (`no_signalling_any_0`, `no_signalling_any_1`, `no_signalling_wigner`,
`no_signalling_friend`, `two_pointers`, `observers_agree`, and any other found while doing it)
keeps its name and its statement, and its proof becomes a short corollary. The old proofs and
the lemmas only they used are deleted: two proofs of one fact are debt. Statements do not
change, so `universe/lean_map.py` and the docs do not either. Report the line delta.

### Phase 5: docs, figure, release

README ("Several qubits": a paragraph "Any number of qubits", rows in "What is proved"),
`papers/qubit.md`, `researches/monomio.md` (the scaling problem is closed without a
parametric monomial). Figure `papers/figures/qubits.svg`, drawn by the orchestrator: the tree,
a gate on qubit `k`, the pairs it mixes. `plans/roadmap.md`: M2 done. Release `v0.6.0`.

## 4. Report and run

Report as in `plans/parametric-mono.md`. One phase per run:

```sh
grok -p "Execute Phase N of plans/n-qubits.md. Read the whole plan first, and section 2 of plans/observer-inside.md and of plans/no-outside.md. Stop at the end of Phase N and print the report." \
  -m grok-4.7 --cwd "$PWD" --output-format json --yolo --max-turns 200 | jq -r '.text'
```

After each run: `git diff`, `./check.sh`, the axioms check, the review, then a commit.
