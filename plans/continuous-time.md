# Plan: continuous time

Executor: `grok` (`grok-4.7`). Orchestrator and reviewer: Claude.
Status: in progress. Milestone M3 of `plans/roadmap.md`, release `v0.7.0`.

| Phase | State   | Goal                                                                   |
| ----- | ------- | ---------------------------------------------------------------------- |
| 1     | done    | spike: partial sums, and the addition law degree by degree (go/no-go)  |
| 2     | done    | the circle: `C_N² + S_N² − 1` is an explicit tail, bounded by `r_N(φ)` |
| 3     | planned | the group law up to a bound, and `r_N` goes to zero                    |
| 4     | planned | the qubit at angle `φ`: the Born pair at `(C_N(φ), S_N(φ))`            |
| 5     | planned | docs, figure, release                                                  |

## 1. Why

Criterion 2 of `plans/roadmap.md`: the symbols `c`, `s` must be tied to an angle `φ`. Today
the kernel knows `c² + s² = 1` (`gC`) and the formal series (`Universe/Series.lean`,
`expCoeff`: the coefficients of `exp(−iφa)` are those of `cos φ · 1 − i sin φ · a`), but no
number `φ` ever enters. Without Mathlib there are no reals to hold `cos φ`. What can be
proved is finite: for rational `φ` and every `N`,

```text
C_N(φ) = Σ_{k≤N} cₖ(φ),   cₖ(x) = cosCoeff k · xᵏ / k!
S_N(φ) = Σ_{k≤N} sₖ(φ),   sₖ(x) = sinCoeff k · xᵏ / k!
```

are rationals, and how far they are from the circle and from the group law is a rational
that can be written down and bounded.

The argument (checked with exact fractions for `N ≤ 13` before writing this plan):

1. **Discrete derivative.** `m · cₘ(x) = −x · sₘ₋₁(x)` and `m · sₘ(x) = x · cₘ₋₁(x)`, because
   `cosCoeff m = −sinCoeff (m−1)` and `sinCoeff m = cosCoeff (m−1)`.
2. **Addition, degree by degree.** For every `m`, `x`, `y`:
   `Σ_{k≤m} (cₖ(x) cₘ₋ₖ(y) − sₖ(x) sₘ₋ₖ(y)) = cₘ(x + y)` and
   `Σ_{k≤m} (sₖ(x) cₘ₋ₖ(y) + cₖ(x) sₘ₋ₖ(y)) = sₘ(x + y)`. Induction on `m` from 1: multiply
   by `m = k + (m − k)` and use 1 on each factor.
3. **The circle.** With `y = −x`: `cₖ` is even, `sₖ` odd, and `cₘ(0) = [m = 0]`. So in
   `C_N² + S_N²` every degree `1 … N` cancels, and what is left is the tail
   `T_N(x) = Σ_{m=N+1}^{2N} Σ_{k=m−N}^{N} (cₖ cₘ₋ₖ + sₖ sₘ₋ₖ)(x)`.
4. **The bound.** In each term at most one product is nonzero (parity), and its absolute
   value is at most `|x|ᵐ / (k! (m−k)!)`. Summed over `k`, that is `(2|x|)ᵐ / m!` (2 again,
   for `eₘ(x) = xᵐ / m!` with `x = y = |x|`). So
   `|C_N(φ)² + S_N(φ)² − 1| ≤ r_N(φ) = Σ_{m=N+1}^{2N} (2|φ|)ᵐ / m!`.
5. **It goes to zero.** If `2|φ| ≤ (N + 2) / 2`, consecutive terms of `r_N` halve, so
   `r_N(φ) ≤ 2 (2|φ|)^{N+1} / (N+1)!`.

Example, `φ = 1`, `N = 8`: `C₈ = 4357/8064`, `S₈ = 4241/5040`,
`C₈² + S₈² − 1 = −6991/1625702400`, `r₈(1) = 373426/212837625`.

Lean core has `Rat` with its order, `Rat.abs` and the `grind` instances for ordered fields
(`Init/Data/Rat`, `Init/Grind/Ordered/Rat.lean`). Phase 1 decides whether that is enough.

Phase 1 note: the spike is a go, in 323 lines. The review made `cosSum`, `sinSum` plain
`sumTo` (no second recursion), proved the index reflection once (`sumTo_reflect`,
`sumTo_reflect_weight`) for both convolutions, and renamed the certificate footer to "righe
dimostrate", since the angle line is an equality of rationals, not a remainder.

Phase 2 note: `exp_add` reuses the Phase 1 skeleton (`sumTo_weight_of_pointwise`,
`sumTo_leibniz`, `series_succ`); `circle_eight` is `decide_cbv`, since `Rat` arithmetic is
irreducible for the kernel's `decide`. The review replaced two local re-proofs with the core
lemmas `Lean.Grind.OrderedAdd.add_le_add` and `Lean.Grind.Semiring.pow_add`.

## 2. Ground rules

Section 2 of `plans/observer-inside.md` and of `plans/no-outside.md` apply in full. In
addition:

- Lean in a new `Universe/Angle.lean`, imported by `Universe.lean`. Python in a new
  `universe/angle.py`, with `fractions.Fraction`, wired into `universe/proofs.py` like the other
  sections.
- Reuse `cosCoeff`, `sinCoeff` and their lemmas from `Universe/Series.lean`; do not define
  them again. In Python, reuse whatever already gives the same coefficients, or move it to one
  place.
- No workaround and no technical debt: no duplicated construction, no helper that returns
  something other than what its name says, no doc left behind. If the cos/sin convolution
  (step 2) and the exponential one (step 4) have the same proof shape, prove it once and
  instantiate it twice. Each phase adds its certificate lines and their `lean_map` keys, and
  updates the line count wherever `tests/test_doc_counts.py` checks it.
- Every theorem is for every `N` and every rational `φ` (or `x`, `y`). Concrete numbers are
  instances: `decide` or `rfl` on `Rat` is allowed, `native_decide` is not.
- `Mono` does not change. This plan touches no polynomial ring until Phase 4.
- Python checks the same facts with exact fractions: every identity for `N ≤ 12` on several
  rationals, and the printed numbers.

## 3. Phases

### Phase 1 (spike): partial sums and the addition law

1. `fact : Nat → Nat` (or the core one if it exists), `cTerm k x`, `sTerm k x : Rat`,
   `cosSum N x`, `sinSum N x : Rat` by recursion on `N`, and a finite sum
   `sumTo : Nat → (Nat → Rat) → Rat` with the lemmas the proofs need (linearity, a shift,
   reversing `k ↦ m − k`).
2. `theorem cTerm_deriv`, `theorem sTerm_deriv`: the discrete derivative (step 1).
3. `theorem angle_add_cos`, `theorem angle_add_sin`: the addition law at degree `m` (step 2),
   for every `m`, `x`, `y`.
4. Python: `universe/angle.py` (`cos_sum`, `sin_sum`, the terms), tests for steps 1 and 2 on
   several rationals, `m ≤ 12`. One certificate line for the addition law.

Go/no-go: at most ~400 lines of Lean. If step 2 does not close, write `researches/tempo.md`
(in Italian, like the other notes) with the design tried and where it broke, mark M3 as
closed by that note in `plans/roadmap.md`, and stop the plan.

### Phase 2: the circle

1. `tailSum N x` (step 3) and `theorem circle_tail`:
   `cosSum N x * cosSum N x + sinSum N x * sinSum N x − 1 = tailSum N x`, for every `N`.
2. `expTerm m x = xᵐ / m!` and `theorem exp_add`, the same law for it:
   `Σ_{k≤m} expTerm k x · expTerm (m−k) y = expTerm m (x + y)`. Shared proof with Phase 1, see
   Ground rules.
3. `remainder N x = Σ_{m=N+1}^{2N} expTerm m (2|x|)` and
   `theorem circle_bound`: `|cosSum N x ^ 2 + sinSum N x ^ 2 − 1| ≤ remainder N x`.
4. Python and certificate: the identity for `N ≤ 12`; the example `φ = 1`, `N = 8` with its
   four rationals and the bound.

### Phase 3: the group law, and the remainder goes to zero

1. `theorem group_bound_cos`: the distance of `cosSum N (x + y)` from
   `cosSum N x · cosSum N y − sinSum N x · sinSum N y` is at most
   `Σ_{m=N+1}^{2N} expTerm m (|x| + |y|)`; `group_bound_sin` likewise. The degrees `≤ N`
   cancel by Phase 1; the rest is bounded as in Phase 2.
2. `theorem remainder_small`: if `2|x| ≤ (N + 2) / 2`, then
   `remainder N x ≤ 2 · expTerm (N + 1) (2|x|)` (step 5).
3. Python and certificate: one line each, with a numeric instance.

### Phase 4: the qubit at angle `φ`

Tie the numbers to the kernel through `Universe/Evaluation.lean`: at the point
`(c, s) = (cosSum N φ, sinSum N φ)`, axis `n = eₓ`, the evolution sends `|0⟩` to a state whose
Born pair is `(cosSum N φ ², sinSum N φ ²)` (reuse `eval_bracket_axis_x` and the column
lemmas). With `circle_bound`, the two weights add up to `1` within `remainder N φ`. A
concrete instance (`φ = 1/2`, a small `N`) by `decide` or `rfl`, if the kernel computes it in
reasonable time; otherwise the general theorem only, and say so in the report. Python: the
same numbers, one certificate line.

### Phase 5: docs, figure, release

README (a paragraph "Continuous time" next to "Time composes", rows in "What is proved"),
`papers/qubit.md`, and the line count everywhere. Figure `papers/figures/tempo.svg`, drawn by
the orchestrator: `(C_N(φ), S_N(φ))` for `N = 1 … 8` spiralling onto the unit circle, with the
band `±r_N`. `plans/roadmap.md`: M3 done. Release `v0.7.0`.

## 4. Report and run

Report as in `plans/parametric-mono.md`. One phase per run:

```sh
grok -p "Execute Phase N of plans/continuous-time.md. Read the whole plan first, and section 2 of plans/observer-inside.md and of plans/no-outside.md. Stop at the end of Phase N and print the report." \
  -m grok-4.7 --cwd "$PWD" --output-format json --yolo --max-turns 200 | jq -r '.text'
```

After each run: `git diff`, `./check.sh`, the axioms check, the review, then a commit.
