# Plan: Wigner's friend

Executor: `grok` (`grok-4.7`). Orchestrator and reviewer: Claude.
Status: in progress.

| Phase | State   | Goal                                                                 |
| ----- | ------- | -------------------------------------------------------------------- |
| 1     | done    | a chain: Wigner reads the friend, and that is reading the system     |
| 2     | done    | the friend's measurement can be undone, until the record is copied   |
| 3     | planned | the rational point: purity `1` when undone, `337/625` after the copy |
| 4     | planned | no-signalling between three parties, for every three-qubit state     |
| 5     | planned | docs, figure, release                                                |

## 1. Why

The observer plan put two apparatuses on the same system (`cnot01`, `cnot02` in
`Universe/Observer.lean`) and proved that they agree. It did not put an observer on an
observer. In Wigner's thought experiment a friend measures a system inside a closed lab, and
Wigner, outside, treats the lab (system and friend) as one quantum system. Two questions follow,
and both have exact answers in this kernel:

- does Wigner, reading the friend, learn what the friend learned? (phase 1)
- is the friend's measurement a fact, or can Wigner undo it? (phase 2)

The answer to the second is the content of the plan: decoherence is relative. While no one has
copied the friend's record, a unitary on the lab restores the system's coherence. Once Wigner
has copied it, the same unitary no longer does. Nothing is postulated; the facts are
permutations of eight cells and Born weights of their entries.

The algebra, checked by the orchestrator, with cells `4i + 2j + k` (system `i`, friend `j`,
Wigner `k`) and `ψ = (α, β)`:

- the friend's `CNOT` is `cnot01` (cells `4↔6`, `5↔7`). Wigner's `CNOT` on the friend,
  `cnot12`, swaps `2↔3` and `6↔7`;
- `cnot12 (cnot01 (ψ ⊗ 0 ⊗ 0)) = α|000⟩ + β|111⟩`, the same state as `two_pointers`: reading
  the friend is reading the system;
- `cnot01 (cnot01 (ψ ⊗ 0 ⊗ 0)) = ψ ⊗ 0 ⊗ 0` (`cnot01` is an involution): the system's
  coherence `α β̄` is back;
- `cnot01 (cnot12 (cnot01 (ψ ⊗ 0 ⊗ 0))) = α|000⟩ + β|101⟩`: the system's off-diagonal is the
  zero polynomial, and Wigner still reads `bornPair ψ`;
- at `ψ = Φ|0⟩`, `c = 3/5`, `s = 4/5`, `n = eₓ` (`α = 3/5`, `β = −4/5 i`): coherence `12/25 i`
  and purity `1` when undone; coherence `0` and purity `337/625` after the copy.

## 2. Ground rules

Section 2 of `plans/observer-inside.md` and of `plans/no-outside.md` apply in full. In
addition:

- Lean goes into `Universe/Observer.lean`, next to `cnot01` and `cnot02`, reusing `Oct`,
  `tensorLeft`, `tensorPair`, `ket0`, `bornOct`, `two_pointers`, `purity`, `eval_purity` and
  `point_purity`. Python goes into `universe/observer.py` (`cnot01`, `cnot02`,
  `_basis_permutation`, `reduced`, `purity`) and `universe/proofs.py`.
- No new `Mono` field: phases 1–3 use only `ψ`, and phase 4 is stated for every `v : Oct`.
- Every new certificate line names its Lean theorems and gets a key in `universe/lean_map.py`;
  the line counts in the docs follow (`tests/test_doc_counts.py`).

## 3. Phases

### Phase 1: a chain of observers

1. `def cnot12 (v : Oct) : Oct`, Wigner's `CNOT` with the friend as control.
   `theorem cnot12_involutive`.
2. `theorem chain_pointers (ψ : Pair)`: `cnot12 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0))`
   is `⟨ψ.a0, [], [], [], [], [], [], ψ.a1⟩`.
3. `theorem chain_is_fanout (ψ : Pair)`: the chain equals `cnot02 (cnot01 …)`, so
   `observers_agree` and `order_irrelevant` apply to it. `theorem chain_agree`: Wigner and the
   friend never disagree (`bornOct` as in `observers_agree`).
4. Python: `cnot12` in `universe/observer.py`; certificate lines for the chain state and the
   agreement, generic `ψ`.

### Phase 2: undoing the friend

1. `def reduceSystem (v : Oct) : Mat`, the state of the system with friend and Wigner traced
   out: entry `(i, i')` is `Σ_{j,k} a_{4i+2j+k} · conj(a_{4i'+2j+k})`. `theorem
reduceSystem_product`: on `ψ ⊗ 0 ⊗ 0` it is `outer ψ`.
2. `theorem friend_undone (ψ : Pair)`: `cnot01 (cnot01 (ψ ⊗ 0 ⊗ 0)) = ψ ⊗ 0 ⊗ 0`, and so the
   off-diagonal of `reduceSystem` is `α β̄` again (as in `coherence_before`).
3. `theorem copy_irreversible (ψ : Pair)`: after `cnot12`, undoing the friend leaves
   `α|000⟩ + β|101⟩`; both off-diagonal entries of `reduceSystem` are the zero polynomial and
   the diagonal is `bornPair ψ` (as in `decoherence`).
4. `theorem wigner_keeps_record (ψ : Pair)`: in that state Wigner's marginal is `bornPair ψ`.
5. Python: the three facts on a generic `ψ`, with `reduced` on three qubits.

### Phase 3: the rational point

1. `theorem point_undone`: at `ψ = Φ|0⟩` and the point of section 1, coherence `12/25 i`,
   purity `1`.
2. `theorem point_copied`: coherence `0`, purity `337/625`, Wigner's weights `9/25`, `16/25`.
   Reuse `eval_purity` and the values of `point_purity`.
3. Python: two numeric lines.

### Phase 4: no-signalling between three parties

1. For every `v : Oct` and the symbolic `U`, a unitary on Wigner's qubit leaves the system's
   Born pair unchanged modulo `(gC, gN)`, and so does a unitary on the friend's qubit.
   `theorem no_signalling_wigner`, `theorem no_signalling_friend`. Reuse the block argument of
   `no_signalling_any_0` and `no_signalling_any_1`: the system's marginal is a sum of
   one-qubit norms.
2. Python: the same on a generic state of three qubits, sixteen reals in a fresh ring.

Go/no-go: over ~300 lines of Lean for item 1, deliver the Wigner case, and state the friend case
as an argument in `papers/qubit.md`.

### Phase 5: docs, figure, release

README ("The observer inside": a paragraph "Wigner's friend", rows in "What is proved",
"Where it is going"), `papers/qubit.md` (a paragraph after the two observers),
`researches/osservatore.md` only if an argument needs room. Figure
`papers/figures/wigner.svg`, drawn by the orchestrator: the chain, and the two orders of
"undo" and "copy" with their purity. Line counts in the seven places. Release `v0.5.0`.

## 4. Report and run

Report as in `plans/parametric-mono.md`. One phase per run:

```sh
grok -p "Execute Phase N of plans/wigner.md. Read the whole plan first, and section 2 of plans/observer-inside.md and of plans/no-outside.md. Stop at the end of Phase N and print the report." \
  -m grok-4.7 --cwd "$PWD" --output-format json --yolo --max-turns 200 | jq -r '.text'
```

After each run: `git diff`, `./check.sh`, the axioms check, the review, then a commit.
