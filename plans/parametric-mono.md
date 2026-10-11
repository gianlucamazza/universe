# Plan: a wider Lean monomial

Executor: `grok` (`grok-4.7`). Orchestrator and reviewer: Claude.
Status: complete. Phase 1 widened `Mono` to 13 exponents (−39 lines); phase 2 proved no-signalling for every `v : Quad`; phase 3 is a measured no-go for a parametric monomial (`researches/monomio.md`); phase 4 updated the docs.

| Phase | State | Goal                                                                  |
| ----- | ----- | --------------------------------------------------------------------- |
| 1     | done  | widen `Mono` from 9 to 13 exponents; no statement changes             |
| 2     | done  | no-signalling and reduced states on a generic two-qubit state in Lean |
| 3     | done  | exploratory: spectator exponents as a parameter, with go/no-go        |
| 4     | done  | docs, figures, research note                                          |

## 1. Why

`researches/osservatore.md` confirms one next step: the Lean monomial is too narrow.
`Universe.Quotient.Mono` has nine `Nat` fields, `c s nx ny nz` for the law and `ar ai br bi`
for one qubit's amplitudes. A generic two-qubit state needs four complex amplitudes, eight
reals. That is why `no_signalling_0` and `no_signalling_1` are proved in Lean only on
`CNOT(|ψ⟩ ⊗ |0⟩)`, while Python proves them on a generic state.

The note also measures the cost: the width is spelled out in `Mono.mul`, `subExp`,
`subExp_mul`, `mul_subExp`, a few `ext` proofs and ten 9-tuples, while the division argument
(`termWeight` to `reduceC_sound`) only reads `c` and `nx`. Extra exponents that are never
peeled and never evaluated are spectators: they should cost tens of lines, not a rewrite.

The plan proceeds from the cheap certain step to the expensive uncertain one.

## 2. Ground rules

Everything in section 2 of `plans/observer-inside.md` still applies: two independent
certificates, no new dependencies, no `sorry`/`admit`/`axiom`/`native_decide`, conventions,
you may build, do not commit, do not touch `papers/figures`, stop and report at the end of
each phase. In addition:

- **Phase 1 changes no statement.** Every existing theorem keeps its name and its statement.
  Only proofs and the definitions in the list below may change. The certificate output must
  be byte-identical before and after (`python -m universe > before.txt`, compare).
- **The division stays blind.** `termWeight`, `peelFirst`, `reduce` and `reduceC_sound` must
  not read the new fields. If a proof of the division needs them, stop and report.
- **Evaluation ignores spectators.** `monoVal` and `evalAt` keep their signature
  (`c s nx ny nz`). The new fields, like `ar ai br bi` today, are not evaluated.
- **No unbounded bullets.** Where a proof enumerates the fields (`ext` with one bullet per
  field, the nine `have` in `subExp_mul`), prefer one generic tactic (`ext <;> simp [...]`,
  `omega`) so that the next widening costs nothing.

## 3. Phases

### Phase 1: thirteen exponents

Add `a2r a2i a3r a3i : Nat` to `Mono`, after `bi`. Then make the library build again:

1. `Mono.one`, `Mono.mul`, `subExp`, `subExp_mul`, `mul_subExp` in `Universe/Quotient.lean`.
2. The ten 9-tuples (`Mono.one`, `cSq`, `sSq`, `nxSq`, `nySq`, `nzSq`, the amplitude
   monomials) become 13-tuples, or better `{ Mono.one with c := 2 }` style so that width does
   not appear again.
3. Every `ext` proof that breaks downstream (`Epistemology`, `Qubit`, `Dynamics`,
   `Composition`, `Observer`, `Evaluation`).

Python needs no change: its `Ring` takes variable names at run time.

Acceptance: `./check.sh` green; certificate output byte-identical; `git diff --stat` reported,
with the line delta per file; `#print axioms` unchanged on `reduce_complete`,
`evolution_unitary`, `pointer_born`, `no_signalling_0`.

### Phase 2: the generic two-qubit state in Lean

With `ar ai br bi a2r a2i a3r a3i` available:

1. `def genericQuad : Quad`, cells `ar + i ai`, `br + i bi`, `a2r + i a2i`, `a3r + i a3i`, in
   the style of `genericPair`.
2. `theorem no_signalling_gen_0` and `no_signalling_gen_1`: for `v = genericQuad`, each
   component of `marginalLeft (applyIU evolution v) − marginalLeft v` is `inIdeal`. Cells 1
   and 2 are no longer empty, so the cross terms `u₀₀ ū₀₁ + u₁₀ ū₁₁` appear; they vanish by
   the off-diagonal of `U†U = I`, which is in `evolution_unitary`.
3. If the proof does not depend on the cells being generic monomials, state it for every
   `v : Quad` and derive the `genericQuad` case; report which form you proved.
4. Python: the existing generic line now cites the new theorems; no new certificate line
   unless a new fact is checked.

Go/no-go: over ~400 lines of Lean for item 2, deliver what is proved and a written argument.

### Phase 3 (exploratory): spectators as a parameter

Question: can the amplitude exponents become a parameter, for example
`structure Mono where law : LawExp; amp : List Nat` with a canonical form, or a width index,
so that three qubits (sixteen reals) need no further edit?

Deliverable is one of:

- the refactor, green, with the same acceptance as phase 1; or
- a no-go note in `researches/monomio.md` (Italian, like the other notes): the design tried,
  where it broke (`DecidableEq`, canonical forms, `ext`), and the cost of the next widening if
  the fields stay explicit.

Hard limit: if `Quotient.lean` grows by more than ~300 lines, stop and write the note.

### Phase 4: documentation

- `README.md`: move the no-signalling row from "Lean on `CNOT(|ψ⟩ ⊗ |0⟩)`" to generic; update
  "How the proofs work" if the monomial changed shape; line count if it changed.
- `papers/qubit.md` section 7 and `researches/osservatore.md`: record that the gap is closed,
  and what phase 3 decided.
- A figure only if a new fact is shown; figures are drawn by the orchestrator.

## 4. Report format

Same as section 7 of `plans/observer-inside.md`, plus the line delta per file.

## 5. How to run

```sh
grok -p "Execute Phase N of plans/parametric-mono.md. Read the whole plan first, and section 2 of plans/observer-inside.md. Stop at the end of Phase N and print the report." \
  -m grok-4.7 --cwd "$PWD" --output-format json --yolo --max-turns 150 | jq -r '.text'
```

After each run: `git diff`, `./check.sh`, the axioms check, the review, then a commit.
