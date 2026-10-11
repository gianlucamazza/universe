# Plan: rotations about different axes

Executor: `grok` (`grok-4.7`). Orchestrator and reviewer: Claude.
Status: planned.

| Phase | State   | Goal                                                                |
| ----- | ------- | ------------------------------------------------------------------- |
| 1     | planned | the Pauli product `(n·σ)(m·σ) = (n·m) I + i (n×m)·σ`, free ring     |
| 2     | planned | `U(c₁, s₁, n) U(c₂, s₂, m) = a I − i (b·σ)`, free ring              |
| 3     | planned | the product stays unitary: `a² + \|b\|² − 1` in `(gC, gN, gC2, gM)` |
| 4     | planned | the rational point, and two rotations that do not commute           |
| 5     | planned | docs, figure, release                                               |

## 1. Why

Time composes only about one axis. `evolution_compose` in `Universe/Symmetry.lean` goes
through `lin_mul`, which needs both factors to share `hamiltonian`, and `evolution2` reuses
the same `H`. The group law of the qubit is wider: two rotations about axes `n` and `m` make
one rotation, and the order matters.

The algebra, checked by the orchestrator:

- `(n·σ)(m·σ) = (n·m) I + i (n×m)·σ` holds in the free ring: no rule is used.
- `U(c₁, s₁, n) U(c₂, s₂, m) = a I − i (b·σ)` with `a = c₁c₂ − s₁s₂ (n·m)` and
  `b = s₁c₂ n + c₁s₂ m + s₁s₂ (n×m)`, again in the free ring. This is stronger than
  `evolution_compose`, which needs `gN`.
- `a² + |b|² = (c₁² + s₁² |n|²)(c₂² + s₂² |m|²)` in the free ring (Euler's four-square
  identity), so `a² + |b|² − 1` lies in `(gC, gN, gC2, gM)`, with `gM = mx² + my² + mz² − 1`.
- With `m = n`, `n×n = 0` in the free ring and `n·n = 1` modulo `gN`: the same-axis law.
- Point `n = eₓ`, `m = e_z`, `c₁ = c₂ = 3/5`, `s₁ = s₂ = 4/5`: `a = 9/25`,
  `b = (12/25, −16/25, 12/25)`, and `81 + 144 + 256 + 144 = 625`.
  `UₙUₘ|0⟩ = (9/25 − 12/25 i)|0⟩ + (−16/25 − 12/25 i)|1⟩`, while
  `UₘUₙ|0⟩ = (9/25 − 12/25 i)|0⟩ + (16/25 − 12/25 i)|1⟩`. The Born weights are `9/25` and
  `16/25` in both orders: the order shows in the phase of `|1⟩`, not in the weights on this
  state.

## 2. Ground rules

Section 2 of `plans/observer-inside.md` applies in full, and section 2 of
`plans/no-outside.md` too. In addition:

- New Lean code goes into `Universe/Qubit.lean` (phase 1), `Universe/Symmetry.lean` (phases
  2–4) and `Universe/Evaluation.lean` (phase 4). Python goes into `universe/proofs.py` and,
  for phase 3 only, `universe/ring.py`.
- Every new certificate line names its Lean theorems and gets a key in `universe/lean_map.py`.
  The line count in the docs follows (`tests/test_doc_counts.py`).
- Widening `Mono` follows phase 1 of `plans/parametric-mono.md`: `mx my mz` after `s2`, the
  four sites only, `{Mono.one with …}`, certificate byte-identical.
- `gM` stays outside `reduce`, like `gA` and `gC2`.

## 3. Phases

### Phase 1: the Pauli product

1. `def axisMat (x y z : Poly) : Mat`, the matrix `x σx + y σy + z σz`, generalizing
   `pauliHamiltonian`. `theorem hamiltonian_axis : hamiltonian = axisMat nx1 ny1 nz1`,
   from `hamiltonian_pauli`.
2. `dot` and `cross` on triples of `Poly`.
3. `theorem pauli_product`: for all `x y z x' y' z'`,
   `matSame (matMul (axisMat x y z) (axisMat x' y' z'))` with
   `lin (dot …) (single Gauss.i Mono.one) (axisMat (cross …))`, in the free ring.
4. Python: one certificate line on a fresh ring `(nx, ny, nz, mx, my, mz)` with no rules,
   using `_axis_hamiltonian`.

### Phase 2: composition about two axes

1. Add the spectators `mx my mz` to `Mono`. Certificate byte-identical; `#print axioms`
   unchanged on `reduce_complete`, `evolution_unitary`, `evolution_compose`.
2. `evolutionM := lin c2P gamma2 (axisMat mx1 my1 mz1)`, next to `evolution2`.
3. `theorem evolution_compose_axes`: `matSame (matMul evolution evolutionM)` with
   `lin a (single (-Gauss.i) Mono.one) (axisMat b)`, for `a` and `b` above, in the free ring.
4. `theorem compose_axes_same`: with `m = n`, the composed pair is the one of
   `evolution_compose`, modulo `gN`. If this costs more than ~100 lines, state it in
   `papers/qubit.md` as an argument and skip the theorem.
5. Python: `_composition` with two generators, ring
   `(c1, s1, c2, s2, nx, ny, nz, mx, my, mz)` with no rules.

Go/no-go: over ~400 lines of Lean for item 3, deliver the entrywise statements that are
proved and a written argument.

### Phase 3: the product stays unitary

1. `inIdeal4 p := ∃ f1 f2 f3 f4, polySame p (pmul f1 gC ++ pmul f2 gN ++ pmul f3 gC2 ++ pmul f4 gM)`,
   in the style of `inIdealCircle`.
2. `theorem compose_axes_norm`: `a² + |b|² − 1` is `inIdeal4`, through the free identity
   `a² + |b|² = (c₁² + s₁² |n|²)(c₂² + s₂² |m|²)` and explicit cofactors.
3. Python: `Poly.certify_extra` takes one extra rule. Add `certify_extras(rules)` for several,
   keep the old method as a call to it, and test it in `tests/test_ring.py`. The certificate
   line must fail without `gM`.

### Phase 4: the point, and order

1. Extend the evaluator to `mx my mz` (`evalAt3`, or a wider `evalAt2`), with an agreement
   lemma in the style of `evalAt2_agrees`.
2. `theorem point_axes`: at the point of section 1, `a`, `b` and `UₙUₘ|0⟩` as above.
3. `theorem rotations_noncommute`: at the same point, `UₙUₘ|0⟩` and `UₘUₙ|0⟩` differ in the
   amplitude of `|1⟩`, with equal Born weights.
4. Python: two numeric lines.

### Phase 5: docs, figure, release

README ("Time composes" and rows in "What is proved"), `papers/qubit.md` (a paragraph after
time composition), `researches/` only if an argument needs room. Figure
`papers/figures/assi.svg`, drawn by the orchestrator: two orders, two images of `|0⟩`. Line
counts in the seven places `tests/test_doc_counts.py` checks. Release `v0.4.0`.

## 4. Report and run

Report as in `plans/parametric-mono.md`. One phase per run:

```sh
grok -p "Execute Phase N of plans/axes.md. Read the whole plan first, and section 2 of plans/observer-inside.md and of plans/no-outside.md. Stop at the end of Phase N and print the report." \
  -m grok-4.7 --cwd "$PWD" --output-format json --yolo --max-turns 150 | jq -r '.text'
```

After each run: `git diff`, `./check.sh`, the axioms check, the review, then a commit.
