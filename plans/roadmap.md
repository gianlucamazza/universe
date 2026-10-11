# Roadmap: to 1.0

Orchestrator: Claude. Executor for code plans: `grok` (`grok-4.7`), one phase per run, with
the gate of section 2 of `plans/observer-inside.md`.

## 1. What "complete" means here

The kernel is a laboratory for the rules of quantum mechanics, not a model of our universe.
It is complete, and version `1.0.0` is due, when all of the following hold:

1. **Every number of qubits.** The structural theorems (tensor product, local unitaries,
   partial trace, no-signalling, observers that agree) are stated and proved in Lean for `n`
   qubits, for every `n`, not for 1, 2 and 3 separately.
2. **Continuous time, as far as it goes without Mathlib.** The symbols `c`, `s` are tied to an
   angle `φ` by partial sums of the series with an explicit, proved remainder.
3. **Two kernels, one set of numbers.** Every rational point the certificate prints is also
   printed by Lean, and a test compares them.
4. **Every limit written down.** What the kernel does not settle (a single outcome, the origin
   of the Born rule, space, fields, gravity) has a note in `researches/` that says why, with
   sources.
5. **Gates.** `./check.sh` green, CI green, zero `sorry`/`admit`/`axiom`/`native_decide`, every
   certificate line mapped in `universe/lean_map.py`.

Anything outside this list is out of scope for 1.0, and is listed in `papers/qubit.md`,
section 8.

## 2. Milestones

| Milestone | Release  | Plan                       | Kind        | Done when                                            |
| --------- | -------- | -------------------------- | ----------- | ---------------------------------------------------- |
| M1        | `v0.5.0` | `plans/wigner.md`          | code        | phases 4–5 done                                      |
| M2        | `v0.6.0` | `plans/n-qubits.md`        | code        | criterion 1                                          |
| M3        | `v0.7.0` | `plans/continuous-time.md` | exploratory | criterion 2, or a no-go note in `researches/`        |
| M4        | `v0.8.0` | `plans/bridge.md`          | code        | criterion 3                                          |
| M5        | `v0.9.0` | none                       | notes       | criterion 4                                          |
| M6        | `v1.0.0` | none                       | release     | criteria 1–5, `papers/qubit.md` rewritten as a whole |

Each plan is written only when the previous milestone is released, so that it starts from the
code as it is.

### M2: `n` qubits

The obstacle measured in `researches/monomio.md` is the monomial: a generic state of `n`
qubits needs `2ⁿ⁺¹` named reals. The way around it is already in the code:
`no_signalling_any_0` is stated for every `v : Quad`, with no generic monomials. M2 follows
that pattern:

- a state of `n` qubits is a function from `Fin (2^n)` (or a list of length `2^n`) to `Poly`;
- a gate on qubit `k` acts through index arithmetic, generalizing `tensorIndexAssoc`;
- the theorems quantify over every state, so `Mono` does not grow.

Targets: local unitaries on qubit `k` commute with those on qubit `l ≠ k`; no-signalling for
every `k`, `n`; partial trace on qubit `k`; a fan-out of `n` observers gives
`α|0…0⟩ + β|1…1⟩` and every pair of them agrees; the existing `Quad` and `Oct` theorems as the
cases `n = 2`, `n = 3`.

Phase 0 is a spike, at most ~300 lines of Lean: no-signalling for `n` parties. If it does not
close, the outcome is a note in `researches/` and M2 shrinks to what the spike proved.

### M3: continuous time

Without Mathlib there are no real numbers to put `cos φ` in. What can be proved is finite:
for rational `φ`, the partial sums `C_N(φ)`, `S_N(φ)` of the series of `expCoeff` satisfy
`|C_N² + S_N² − 1| ≤ r_N(φ)` and the group law up to a similar bound, with `r_N → 0` written
as an explicit rational. The plan is exploratory: phase 1 decides, with a go/no-go, whether
the bounds fit in `Rat` arithmetic and `decide`/`grind`; otherwise a note says where it breaks.

### M4: the bridge

Lean evaluates the rational points with `#eval` (or a small `lake exe`), the output is written
in the same format as the certificate's numeric lines, and a test in `tests/` compares the two.
The kernels stay independent; only their numbers meet.

### M5: the limits, in writing

Notes in Italian, like the others in `researches/`, each with sources:

- `researches/misura.md`: the kernel produces the Born pair, never one outcome; what the
  observer theorems settle and what they leave to an interpretation.
- `researches/born.md`: the Born rule is the definition of `Obs` here. What Gleason's theorem
  derives (dimension ≥ 3) and Busch's version for effects (also dimension 2), and what that
  would cost in this kernel.
- `researches/distanza.md`: what separates the kernel from our universe: scale, space,
  fields, gravity, the arrow of time.

## 3. Order and cadence

M1 → M2 → M3 → M4 → M5 → M6. M5 does not depend on code and can be written while a code
phase runs. Each phase: grok run, review of the diff, `./check.sh`, axioms, commit, push, CI.
Each milestone: README, `papers/qubit.md`, a figure if a new fact can be drawn, release.
