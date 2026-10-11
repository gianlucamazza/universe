# Plan: the observer inside the universe

Executor: `grok` (`grok-4.7`). Orchestrator and reviewer: Claude.
Status: complete. Every phase is done and pushed.

| Phase | State | Commit    | Key theorems                                                       |
| ----- | ----- | --------- | ------------------------------------------------------------------ |
| 1     | done  | `9996340` | `cnot_involutive`, `cnot_norm`, `product_det`, `point_not_product` |
| 2     | done  | `919b254` | `decoherence`, `pointer_born`, `purity_sphere`, `point_purity`     |
| 3     | done  | `09a8442` | `two_pointers`, `observers_agree`, `order_irrelevant`              |
| 4     | done  | `abae267` | `no_signalling_0`, `no_signalling_1` (Lean on `CNOT(\|ψ⟩ ⊗ \|0⟩)`) |
| 5     | done  | —         | `researches/osservatore.md`                                        |

Outcome: `Obs` is derived (`pointer_born`). The next step the note confirms is a parametric
`Mono`; a preferred basis and real `cos φ` are rejected with arguments.

## 1. Why

Today `Obs` is an axiom: the computational-basis measurement is handed to the kernel from
outside. A real universe has no outside. The goal of this plan is to turn `Obs` into a
theorem: a second qubit (the _apparatus_) interacts with the system through `CNOT`, and the
Born weights of the system appear as the pointer statistics of the apparatus, computed with
the dynamics and the partial trace only. Along the way the kernel gains its first entangled
state, so composition stops being limited to product states and `U ⊗ I`.

The result we want to be able to state, exactly and in both certificates:

> After `CNOT` couples `Φ|ψ⟩` to an apparatus in `|0⟩`, the reduced state of the system is
> diagonal, its diagonal is `bornPair (Φ|ψ⟩)`, the apparatus reads the same distribution, two
> apparatuses never disagree, and nothing done locally to an apparatus changes the system's
> statistics.

## 2. Ground rules (read before any edit)

- **Two independent certificates.** Python (`universe/`) and Lean (`Universe/`) prove the same
  facts separately. Neither is generated from the other. Every new fact gets a Python line in
  `python -m universe` and a Lean theorem, or an explicit note saying which side carries it.
- **No new dependencies.** No Mathlib, no new Python packages.
- **No escape hatches.** No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `partial`.
  `#print axioms` on every new theorem must show only `propext`, `Classical.choice`,
  `Quot.sound`.
- **The Lean monomial is fixed.** `Universe.Quotient.Mono` has exactly nine exponents
  (`c s nx ny nz ar ai br bi`). Do **not** add variables. Everything in this plan is designed to
  fit them: the apparatus always starts in `ket0`, so its amplitudes are constants. If a step
  seems to need new variables, stop and report instead of refactoring `Quotient.lean`.
- **Conventions.** Docstrings, Lean module headers and certificate output are in Italian, like
  the existing code. `README.md` is in English. Lean style follows `Composition.lean`: `@[ext]`
  structures, `polySame`/`pairSame`/`quadSame` for coefficient equality, `simp only` with
  explicit lemma lists. Python follows `ring.py`/`ontology.py`: frozen dataclasses, exact
  `Gauss`, `ValueError` with Italian messages.
- **You may build.** Unlike the usual edit-only delegation, Lean proofs need feedback: run
  `lake build` (PATH: `$HOME/.elan/bin`) and `./check.sh` as often as needed.
- **Do not commit, do not push.** Stop at the end of each phase and report (section 7).
- **Do not touch** finished theorems except to add `@[simp]` or to generalize a lemma
  without changing its statement. Renaming a cited theorem breaks `tests/test_lean_citations.py`.

## 3. Map of what already exists

| Need                                  | Lean                                                      | Python                                   |
| ------------------------------------- | --------------------------------------------------------- | ---------------------------------------- |
| Polynomial, product, conjugate        | `Quotient.Poly`, `Dynamics.pmul`, `conjP`, `psub`         | `ring.Poly`                              |
| Coefficient equality                  | `Dynamics.polySame`, `coeffOf`                            | `Poly.__eq__` after reduction            |
| Ideal membership with cofactors       | `Dynamics.inIdeal`, `gC`, `gN`, `gA`                      | `certification`, `certify_extra`         |
| 2×2 matrix                            | `Dynamics.Mat`, `matMul`, `matDagger`, `matScale`         | `ontology.Operator`                      |
| One qubit, two qubits, three qubits   | `Composition.Pair`, `Quad`, `Oct`                         | `ontology.State`                         |
| Tensor, index `2i + k`, `4i + 2j + k` | `tensorPair`, `tensorLeft`, `tensorRight`                 | `tensor_state`, `tensor_index`           |
| `U ⊗ I`, `I ⊗ U`, `U ⊗ I ⊗ I`         | `applyUI`, `applyIU`, `applyUII`                          | `Operator.tensor`                        |
| Born weights, marginals               | `columnBorn`, `bornPair`, `marginalLeft/Right`, `bornOct` | `born`, `marginal`                       |
| The evolution and its unitarity       | `Qubit.evolution`, `evolution_unitary`                    | `QubitUniverse.U`                        |
| Rational point `c=3/5, s=4/5, n=eₓ`   | `point_prob0`, `point_prob1`, `point_unitary`             | `proofs.py`, "Corollario"                |
| Generic state, sphere                 | `genericPair`, `gA`, `marginal_left_sphere`               | `QubitUniverse.generic`, `certify_extra` |

Read `Composition.lean` in full before starting; it is the template for every new proof.

## 4. Phases

Each phase ends green on `./check.sh` and is reviewable on its own. Names below are the
target names; keep them unless they clash, and report any rename.

New files: `Universe/Observer.lean` (imported by `Universe.lean`), `universe/observer.py`,
`tests/test_observer.py`. New certificate section: `Osservatore`.

### Phase 1: CNOT and the first entangled state

Lean, `Universe/Observer.lean`, namespace `Universe.Observer`:

1. `def applyCNOT (v : Quad) : Quad := ⟨v.a0, v.a1, v.a3, v.a2⟩`
   (control left, target right; on `2i + k` it swaps `|10⟩` and `|11⟩`).
2. `theorem cnot_involutive (v) : applyCNOT (applyCNOT v) = v`.
3. `theorem cnot_ket0 (ψ : Pair) : applyCNOT (tensorPair ψ ket0) = ⟨ψ.a0, [], [], ψ.a1⟩`
   (via `tensor_idle_right`). This is `α|00⟩ + β|11⟩`.
4. `def quadNorm (v : Quad) : Poly` (sum of the four `columnBorn`) and
   `theorem cnot_norm (v) : polySame (quadNorm (applyCNOT v)) (quadNorm v)`. It holds in the
   free ring, with no ideal needed.
5. Product test. `def quadDet (v : Quad) : Poly := psub (pmul v.a0 v.a3) (pmul v.a1 v.a2)`.
   - `theorem product_det (ψ φ) : polySame (quadDet (tensorPair ψ φ)) []`. Every product
     state has determinant zero. This needs commutativity/associativity of `pmul` at the
     `coeffOf` level; reuse what `slide_right`, `assoc_row` and `columnBorn_pmul` already
     use before writing new lemmas.
   - `theorem entangled_det (ψ) : polySame (quadDet (applyCNOT (tensorPair ψ ket0))) (pmul ψ.a0 ψ.a1)`.
6. Entanglement at the rational point. On `Φ|0⟩` at `c = 3/5, s = 4/5, n = eₓ` the
   amplitudes are `3/5` and `−4/5 i`, so the determinant evaluates to `−12/25 i ≠ 0`.
   - `theorem point_entangled`: the evaluated determinant is `−12/25 i`. Reuse the evaluation
     path behind `point_prob0`.
   - `theorem point_not_product`: there are no numeric pairs `(x0, x1)`, `(y0, y1)` in `Gauss`
     whose tensor equals that evaluated `Quad`. The proof is the numeric version of
     `product_det` plus the nonzero value. If `Ring.lean` lacks `mul_comm`/`mul_assoc` for
     `Gauss`, add them there.

Python, `universe/observer.py`:

- `cnot(ring) -> Operator` (4×4 from `from_rows`), `determinant_2x2(state) -> Poly`.
- Certificate lines (`proofs.py`, section `Osservatore`):
  - `CNOT² = I`, and `‖CNOT v‖² = ‖v‖²` on a generic two-qubit state. Build that state in a
    fresh `Ring` with 8 real variables; Python is not bound to the nine Lean exponents.
  - `|ψ⟩ ⊗ |φ⟩` has determinant zero (generic factors, fresh ring).
  - `CNOT(Φ|0⟩ ⊗ |0⟩)` at the rational point has determinant `−12/25 i`, so it is not a
    product.

Acceptance: `./check.sh` green, the certificate grows by 3–4 lines, and the README "What is
proved" table gains a `Composition` row for CNOT/entanglement.

### Phase 2: reduced states and decoherence

Lean:

1. `def reduceLeft (v : Quad) : Mat`, the partial trace over the right factor:
   - `a00 = columnBorn a0 ++ columnBorn a1`
   - `a01 = pmul a0 (conjP a2) ++ pmul a1 (conjP a3)`
   - `a10 = pmul a2 (conjP a0) ++ pmul a3 (conjP a1)`
   - `a11 = columnBorn a2 ++ columnBorn a3`

   `reduceRight` is defined symmetrically.

2. `theorem reduceLeft_diag (v)`: the diagonal of `reduceLeft v` is `marginalLeft v` (expected
   `rfl`). This ties the new object to the existing marginals.
3. `def outer (ψ : Pair) : Mat`, which is `|ψ⟩⟨ψ|`.
   `theorem reduce_product (ψ φ) : matSame (reduceLeft (tensorPair ψ φ)) (matScale (normPair φ) (outer ψ))`.
   Without interaction the system stays pure, up to `‖φ‖²`.
4. `theorem coherence_before (ψ)`: `(reduceLeft (tensorPair ψ ket0)).a01` is `polySame` to
   `pmul ψ.a0 (conjP ψ.a1)`, so the coherence `α β̄` is present.
5. **`theorem decoherence (ψ)`**: `reduceLeft (applyCNOT (tensorPair ψ ket0))` has
   `a01` and `a10` `polySame []` and diagonal `bornPair ψ`. This holds in the free ring.
6. **`theorem pointer_born (ψ)`**: `reduceRight (applyCNOT (tensorPair (applyMat evolution ψ) ket0))`
   is diagonal with diagonal `bornPair (applyMat evolution ψ)`. The apparatus, which is a
   subsystem, reads the Born weights of the evolved system. This is the central theorem of
   the plan; its docstring must say that `Obs` is now derived.
7. Purity. `def matTrace`, `def purity (ρ : Mat) : Poly := matTrace (matMul ρ ρ)`.
   - Before the interaction: `purity (outer ψ)` is `polySame (pmul ‖ψ‖² ‖ψ‖²)`.
   - After: `purity` of the decohered state is `|α|⁴ + |β|⁴`.
   - On the sphere: `1 − purity − 2|α|²|β|²` lies in `(gA)`, with an explicit cofactor
     following `marginal_left_sphere`.
   - At the rational point: purity `= 337/625 < 1`, which shows the system's state is mixed.

Python: `reduced(state, factor, left, right) -> Operator`, `purity(op) -> Poly`.
Certificate lines: decoherence (off-diagonal zero), `pointer_born` on `Φ|0⟩` and on the
generic state, purity `337/625` at the point.

Acceptance: green; README gains a new table layer, `Observer`; `Universe.lean` header lists
the new module.

### Phase 3: two observers agree

Three qubits: system, apparatus A, apparatus B. Cell `4i + 2j + k` as in `Oct`.

Lean:

1. `def cnot01 (v : Oct) : Oct` swaps cells `4↔6`, `5↔7`; `def cnot02 (v : Oct) : Oct` swaps
   `4↔5`, `6↔7`.
2. `theorem two_pointers (ψ)`: `cnot02 (cnot01 (tensorLeft (tensorPair ψ ket0) ket0))` is the
   `Oct` with `ψ.a0` in cell 0, `ψ.a1` in cell 7 and `[]` elsewhere. That is the GHZ form
   `α|000⟩ + β|111⟩`.
3. `theorem observers_agree (ψ)`: `bornOct` of that state is `[]` on cells 1–6, so the
   probability that A and B disagree is zero, exactly, for every `ψ`.
4. `theorem order_irrelevant (ψ)`: `cnot01 ∘ cnot02` and `cnot02 ∘ cnot01` give the same state.
   The two observers commute.
5. With `tensor_assoc`, the same holds if the state is built as `tensorRight`.

Python: generic 3-qubit `CNOT`s via `Operator.tensor` and permutation matrices. Certificate
line: "due osservatori non sono mai in disaccordo".

### Phase 4 (exploratory): no-signalling

Since phase 2, `Universe/Evaluation.lean` holds the generic evaluation lemmas
(`eval_polySame`, `eval_pmul`, `eval_conj`). Reuse them; new generic lemmas go there,
observer facts go in `Observer.lean`. `papers/qubit.md` section 7 describes phases 1–3;
extend it rather than duplicating it.

Claim: a local unitary on the apparatus does not change the system's statistics.

- Lean, within the nine exponents: take `w = applyCNOT (tensorPair ψ ket0)` and the apparatus
  evolution `applyIU evolution w`. Prove that `marginalLeft (applyIU evolution w)` minus
  `marginalLeft w` lies in `(gC, gN)` with cofactors. The column norms of `evolution` are `1`
  modulo `δ` (`evolution_unitary`). State it as `inIdeal` per component, like
  `ground_prob_sum`.
- Python: prove it for a **fully generic** two-qubit state and a generic `U` satisfying the
  quotient. Use a fresh ring if needed. Python can reach that generality; Lean cannot without
  new variables.
- Document the split in the README row, the way `kronecker_ui_gen` documents `|φ⟩ = |0⟩`.

Go/no-go: if the Lean proof needs more than ~300 lines or new `Mono` fields, deliver the
Python line and a written argument in `researches/osservatore.md`, and report it as a no-go
for Lean.

### Phase 5 (exploratory): research note and next questions

`papers/qubit.md` section 7 already states what phases 1–3 prove. Write `researches/osservatore.md` (Italian, same tone and length as
`researches/associazione.md`):

- the argument, not the inventory: why decoherence and agreement hold in the free ring;
- what "Obs derived" means here and what it does **not** mean: no collapse, no single outcome,
  no preferred basis derived (the basis is fixed by `CNOT`);
- which identities are free-ring, which need `(gC, gN)`, which need `gA`;
- dead ends met during phases 1–4, with the reason;
- three candidate next steps, each with a cost estimate and the blocking obstacle. Seed list,
  to be confirmed or rejected with arguments:
  1. a preferred basis from the interaction (einselection) instead of a fixed `CNOT`;
  2. a general two-qubit Hamiltonian, which requires lifting the 9-variable `Mono` to a
     parametric one (estimate the refactor of `Quotient.lean`);
  3. linking `c, s` to real `cos φ, sin φ` without Mathlib, and whether that is worth it.

## 5. Documentation updates (every phase)

- `README.md`: rows in "What is proved", the line count in "Run", and one paragraph in
  "Reading" per phase. Keep the existing voice: short declarative sentences, no marketing.
- `Universe.lean` header and `universe/__init__.py` docstring: one or two sentences each.
- `papers/qubit.md`: only if a statement there becomes false or incomplete.
- The certificate line count appears in `README.md`, `papers/qubit.md`, `researches/*.md`:
  `grep -rn 'stampa\|prints' README.md papers researches` and update every occurrence.
- Every `Universe.<Module>.<name>` written in Python or docs must exist. The citation test
  enforces this.

## 6. Risks

| Risk                                                          | Signal                             | Response                                                                   |
| ------------------------------------------------------------- | ---------------------------------- | -------------------------------------------------------------------------- |
| `pmul` commutativity at `coeffOf` level is missing or painful | `product_det` takes over 150 lines | Prove one general lemma `polySame (pmul p q) (pmul q p)` first, then reuse |
| `polySame` vs `=` mismatch                                    | `ext` goals with list order        | State results with `polySame`/`quadSame`, as `kronecker_iu_gen` does       |
| Evaluation at the point is ad hoc                             | Can't reuse `point_prob0`          | Factor a small `evalPoly` lemma set; don't duplicate                       |
| Certificate slows down                                        | `python -m universe` over 2 s      | Fresh small rings per identity; no 16-variable products                    |
| Scope creep into `Quotient.lean`                              | Edits to `reduce`/`Mono`           | Stop and report (rule in section 2)                                        |

## 7. Report format (end of each phase)

```
Phase N: done | partial | blocked
Theorems added: <list, with file:line>
Certificate: <old> → <new> lines, all [dimostrato]
#print axioms: <ok | list>
./check.sh: <ok | failing step + output tail>
Deviations from the plan: <names, statements, reasons>
Open problems: <list>
```

## 8. How to run (orchestrator)

One phase per run, review and commit between phases:

```sh
grok -p "Execute Phase N of plans/observer-inside.md. Read the whole plan first. Stop at the end of Phase N and print the report of section 7." \
  -m grok-4.7 --cwd "$PWD" --output-format json --yolo --max-turns 120 | jq -r '.text'
```

After each run: `git diff`, `./check.sh`, the axioms check, the best-practices review, then a
commit in the existing style (`feat: prove ...`).
