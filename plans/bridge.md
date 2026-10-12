# Plan: the bridge

Executor: `grok` (`grok-4.7`). Orchestrator and reviewer: Claude.
Status: complete. All four phases are done and pushed. Milestone M4 of `plans/roadmap.md`, release `v0.8.0`.

| Phase | State | Goal                                                                  |
| ----- | ----- | --------------------------------------------------------------------- |
| 1     | done  | spike: `lake exe points` prints one rational point, Python compares   |
| 2     | done  | every rational point of the certificate, in Lean and in Python        |
| 3     | done  | CI: the Lean job checks the file, the Python job compares the numbers |
| 4     | done  | docs, release                                                         |

## 1. Why

Criterion 3 of `plans/roadmap.md`: every rational point the certificate prints is also
printed by Lean, and a test compares them. Today the two kernels meet only in names
(`universe/lean_map.py`, `tests/test_lean_map.py`): a certificate line cites the Lean theorems
that prove it, but no test checks that the numbers Lean proves are the numbers Python prints.
A drift in one definition (an index order, a sign of `i`, a conjugate) would go unseen as long
as each kernel is consistent with itself.

The kernels stay independent: Python never calls Lean, Lean never reads Python. Only their
numbers meet, in a committed file:

```text
points.txt          # one line per point: key, then exact rationals (re, im)
lake exe points     # Lean prints points.txt from its own definitions
universe/points.py  # Python computes the same keys from its own definitions
```

CI has a Python job without Lean and a Lean job without Python. So the Lean job checks that
`lake exe points` reproduces `points.txt` byte for byte, and a Python test checks that
`universe/points.py` gives the same values, read as `Fraction`, not as strings.

Phase 1 note: `lake exe points` runs in half a second. The review moved the key list from
`Main.lean` into `Universe.Points.table`, so `Main` only prints and every new point is added
in one place, next to its `example`.

Phase 2 note: 95 keys. The first run left out the eight cell weights, the `c = 0` sample and
the two energies, because no numeric theorem had them as left-hand side; the review asked for
those theorems (`point_cells`, `point_cnot_sample`, with `eval_keepFlip`) instead of a smaller
criterion. Every rational result the certificate prints is now a key: only the inputs `1/2`
and `4/5` are not. `universe/points.py` imports only public names from `universe/proofs.py`.

## 2. Ground rules

Section 2 of `plans/observer-inside.md` and of `plans/no-outside.md` apply in full. In
addition:

- Lean: `Universe/Points.lean` (the table of points, built only from the definitions the
  `point_*` theorems use: `evalAt`, `evalAt2`, `evalAt3`, `pointC`, `pointS`, `cosSum`, …) and a
  `lean_exe points` in `lakefile.toml` with a small `Main`. No new theorem is needed, but each
  key must name the Lean theorem that proves its value, and a Lean `example` (or the theorem
  itself, by `rfl`/`decide_cbv`) checks that the printed value is the proved one. The printed
  number and the proved number must be the same term, not two computations: each entry is a
  `def` whose body is the left-hand side of its theorem, and `example : entry = value :=
theorem` ties them.
- Python: `universe/points.py` builds the same table from the certificate's own computations
  (reuse the functions `proofs.py` already calls; do not recompute a point a second way).
- Format: `key re im` with `re`, `im` as `p/q` in lowest terms (or an integer), one point per
  line, keys sorted. A real point has `im = 0`. Vectors and matrices are flattened into keys
  (`bell.00`, `bell.11`, …).
- `points.txt` is generated, never edited by hand. `lake exe points > points.txt` is the only
  way to change it; the Python test never writes it.
- No workaround and no technical debt: no duplicated construction, no helper that returns
  something other than what its name says, no doc left behind.

## 3. Phases

### Phase 1 (spike): one point

1. `Universe/Points.lean` with one entry, `p0` and `p1` of `point_prob0`/`point_prob1`
   (`9/25`, `16/25`), and `lean_exe points`. `lake exe points > points.txt`.
2. `universe/points.py` with the same entry; `tests/test_points.py` parses `points.txt` and
   compares.

A check before writing this plan: `#eval (evalAt (3/5) (4/5) 1 0 0 (bornPair (applyMat
evolution ket0)).a1).re` prints `16/25`, and `#eval cosSum 8 1` prints `4357/8064`. Only the
quotient dynamics (`qubitDyn`, `gateDyn`) are `noncomputable`, and no point uses them.

Go/no-go: if `evalAt` on the polynomial terms does not run in compiled code in reasonable time
(a second), or a definition is `noncomputable`, write the obstacle in the report and propose
the fix (e.g. a computable mirror proved equal to the original); do not add a second
definition without a proof that it is the same.

### Phase 2: every point

Every rational point the certificate prints (`python -m universe | grep -E '[0-9]+/[0-9]+'`):
the qubit point, Bell and the determinant, purity, the friend undone and copied, the partial
measurements, Lüders and repeatability, `V(U|0⟩)`, the two axes and the non-commuting orders,
the composed angle, and the Tempo points. Each key cites its theorem in a comment in
`Universe/Points.lean` and in `universe/points.py`.

### Phase 3: CI

`.github/workflows/check.yml`: in the `lean` job, a step `lake exe points | diff - points.txt`;
the Python job already runs `tests/`. `check.sh`: the same diff after `lake build`. A test that
every key of `points.txt` is computed by Python and vice versa.

### Phase 4: docs, release

README ("Running it" and the guards paragraph: the bridge), `papers/qubit.md`, `CITATION.cff`
if it lists the checks. `plans/roadmap.md`: M4 done. Release `v0.8.0`.

## 4. Report and run

Report as in `plans/parametric-mono.md`. One phase per run:

```sh
grok -p "Execute Phase N of plans/bridge.md. Read the whole plan first, and section 2 of plans/observer-inside.md and of plans/no-outside.md. Stop at the end of Phase N and print the report." \
  -m grok-4.7 --cwd "$PWD" --output-format json --yolo --max-turns 200 | jq -r '.text'
```

After each run: `git diff`, `./check.sh`, the axioms check, the review, then a commit.
