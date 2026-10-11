# Plan: nothing given from outside

Executor: `grok` (`grok-4.7`). Orchestrator and reviewer: Claude.
Status: in progress; phases 1–3 done.

| Phase | State | Goal                                                                  |
| ----- | ----- | --------------------------------------------------------------------- |
| 1     | done  | energy is conserved                                                   |
| 2     | done  | the interaction comes from a Hamiltonian; `CNOT` is one of its points |
| 3     | done  | partial measurement: coherence shrinks by `⟨0\|U\|0⟩`                 |
| 4     | open  | reading the pointer: the conditional state and repeatability          |
| 5     | open  | a unitary change of basis is the same universe                        |
| 6     | open  | time composes: `U(φ₁) U(φ₂) = U(φ₁ + φ₂)`                             |
| 7     | open  | docs and figures                                                      |

## 1. Why

The observer plan derived `Obs`, but the model still takes some things from outside or
leaves them unproved:

- the interaction is a hand-written permutation (`applyCNOT`), not a dynamics;
- measurement is always perfect, and nothing says what the system is _after_ a reading;
- the law of motion is a family of unitaries with no time composition and no conserved
  quantity;
- the README's identity principle (an isomorphism commuting with `Φ` and `Obs`) has only
  associativity as an instance.

Each phase removes one of these. Phases 1, 3, 4 and 5 fit the current monomial; phase 2
needs 4×4 operators; phase 6 needs two spectator exponents.

## 2. Ground rules

Section 2 of `plans/observer-inside.md` applies in full. In addition:

- New Lean files: `Universe/Interaction.lean` (phases 2–4) and `Universe/Symmetry.lean`
  (phases 1, 5, 6), both imported by `Universe.lean`. New Python module:
  `universe/interaction.py`. Each new certificate line names its Lean theorem.
- Widening `Mono` follows the phase-1 technique of `plans/parametric-mono.md`: spectators
  after the last field, `{Mono.one with …}`, no per-field bullets, certificate unchanged.
- Rational points are part of every phase: each new fact gets a numeric line at a point
  of the circle, so it can be drawn. The orchestrator draws the figures.

## 3. Phases

### Phase 1: energy is conserved

`U = c I − i s H` commutes with `H` in the free ring: `U H` and `H U` are both
`c H − i s H²`.

1. `theorem evolution_commutes_hamiltonian`: `matSame (matMul evolution hamiltonian)
(matMul hamiltonian evolution)`.
2. `theorem energy_conserved`: on the generic state, `⟨Uψ|H|Uψ⟩ − ⟨ψ|H|ψ⟩` lies in
   `(gC, gN)`. Route: `U†HU = U†UH` by the commutation, then `U†U − I` is `δ`.
3. Python: `expectation(evolve(ψ), H) − expectation(ψ, H)` has remainder zero.
4. Point: at `c = 3/5, s = 4/5, n = eₓ` and `ψ = |0⟩`, `⟨H⟩ = 0` before and after; pick
   one state with nonzero energy (for example `|0⟩` along `n = e_z`, energy 1) for the
   numeric line.

### Phase 2: the interaction comes from a Hamiltonian

Generator `G = |1⟩⟨1| ⊗ (n·σ)` on two qubits, cells `2i + k`. It is not an involution:
`G² = |1⟩⟨1| ⊗ I` (modulo `gN`) and `G³ = G`.

1. 4×4 operators over `Poly`: reuse `Quad` as the state and define the operator as the
   action on `Quad` (like `applyUI`), or a `Mat4` structure. Prefer the least new code.
2. A second collapse in `Universe/Series.lean`: if `a³ = a`, the coefficient of `φⁿ/n!` in
   `exp(−iφ a)` is that of `(1 − a²) + cos φ · a² − i sin φ · a`. Prove it in the style of
   `expCoeff` (formal coefficients, factorial removed). Name: `expCoeff_idem`.
3. Instance on `G`: `exp(−iφ G) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`, the controlled evolution.
   `theorem controlled_from_hamiltonian`.
4. `theorem cnot_point`: at `c = 0, s = 1, n = eₓ`, `U = −i X`, so the controlled evolution
   is `CNOT` followed by the phase `−i` on the control's `|1⟩` (a local `Z`-rotation).
   On `|ψ⟩ ⊗ |0⟩` it gives `α|00⟩ − i β|11⟩`, and `decoherence` and `pointer_born` hold
   unchanged because the phase drops out of every Born weight. State that link explicitly.
5. Python: the same generator, `G³ = G` with remainder zero, the controlled evolution, the
   `c = 0` point.

### Phase 3: partial measurement

With the controlled evolution as coupling and the apparatus in `|0⟩`, the state is
`α|0⟩|0⟩ + β|1⟩ U|0⟩`.

1. `theorem partial_coherence`: the off-diagonal of the reduced system is
   `α β̄ · conj(⟨0|U|0⟩)` in the free ring, with `⟨0|U|0⟩ = c − i s nz`.
2. `theorem partial_diagonal`: the diagonal is the Born pair modulo `(gC, gN)` (the column
   norm of `U`).
3. Points, along `n = eₓ`, `ψ = Φ|0⟩` at `(3/5, 4/5)` (`α = 3/5`, `β = −4/5 i`):

   | coupling `(c, s)` | coherence  | purity        |
   | ----------------- | ---------- | ------------- |
   | `(1, 0)`          | `12/25 i`  | `1`           |
   | `(3/5, 4/5)`      | `36/125 i` | `11017/15625` |
   | `(0, 1)`          | `0`        | `337/625`     |

   The coupling uses its own `(c, s)` while `ψ` is fixed; if one set of symbols cannot
   carry both, evaluate `ψ` first and state the points as numeric facts. These values were
   computed in exact arithmetic by the orchestrator.

4. Python: the three points and the general factor.

### Phase 4: reading the pointer

1. `def condition (k : Fin 2) (v : Quad) : Pair`: the system's unnormalized state when the
   apparatus reads `k`, by projecting the apparatus on `|k⟩`.
2. `theorem luders`: after `CNOT` on `|ψ⟩ ⊗ |0⟩`, `condition 0` is `(α, 0)` and
   `condition 1` is `(0, β)`; their norms are `bornPair ψ`. The update rule is a theorem.
3. `theorem repeatable`: a second `CNOT` to a fresh apparatus, applied to the conditioned
   state, reads `k` with weight equal to the norm and the other outcome with weight zero.
4. Python: both, generic `ψ`.

### Phase 5: a change of basis is the same universe

For any `V : Mat` with `V†V` and `VV†` equal to `I` (as hypotheses, in the free ring or
modulo an ideal), the universe `(V X, V U V†, Born in the basis V|k⟩)` is isomorphic to
the original:

1. `theorem conj_evolution`: `V (U ψ) = (V U V†) (V ψ)`.
2. `theorem conj_born`: the Born weights of `Vψ` in the basis `V|k⟩` equal those of `ψ`.
3. Python: a concrete `V`, for example `U` itself at the rational point, or a symbolic `V`
   in a fresh ring with its unitarity as rules.

### Phase 6: time composes

Add spectators `c2 s2` to `Mono`. With `c = c₁c₂ − s₁s₂` and `s = s₁c₂ + c₁s₂`:

1. `theorem evolution_compose`: `U(c₁, s₁) U(c₂, s₂) − U(c, s)` lies in the ideal of `gN`
   alone: `H² = I` is the only rule used. The circle is not needed for the group law.
2. `theorem compose_circle`: if both pairs lie on the circle, so does `(c, s)`, in the ideal
   `(gC₁, gC₂)`. This needs `gC₂ = c2² + s2² − 1` as a generator outside `reduce`, like
   `gA`.
3. Python: both, in a fresh ring.

Go/no-go: if `reduce` would have to peel `c2`, stop: state the result with explicit
cofactors (`inIdeal3`-style) instead.

### Phase 7: docs and figures

README (one section, "Nothing from outside", and rows in "What is proved"),
`papers/qubit.md` (a new section), `researches/` only if an argument needs room. Figures:
the controlled evolution circuit with its three points, and the coherence/purity
continuum. Drawn by the orchestrator.

## 4. Report and run

Report as in `plans/parametric-mono.md`. One phase per run:

```sh
grok -p "Execute Phase N of plans/no-outside.md. Read the whole plan first, and section 2 of plans/observer-inside.md. Stop at the end of Phase N and print the report." \
  -m grok-4.7 --cwd "$PWD" --output-format json --yolo --max-turns 150 | jq -r '.text'
```
