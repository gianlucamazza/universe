# universe

[![check](https://github.com/gianlucamazza/universe/actions/workflows/check.yml/badge.svg)](https://github.com/gianlucamazza/universe/actions/workflows/check.yml)

A tiny quantum universe in which every law is a proved theorem.

## In plain words

Quantum mechanics describes a world with three ingredients: the states it can be in, the rule by which those states change in time, and what can be observed. This repository builds the smallest such world, a single qubit and then a few qubits together, and proves every statement about it **exactly**. There are no floating-point numbers, no approximations, and no "it looked right in a simulation".

Every fact is checked twice, independently:

- a Python program recomputes it with exact fractions and fails if anything is off;
- a Lean 4 proof is checked by a machine.

![Map of the project: states, law and observation, each law checked by Python and by Lean](papers/figures/mappa.svg)

**Nothing here is new physics.** Every statement is textbook quantum mechanics. What is new is the object: a complete, certified model in which nothing is assumed without being written down and proved.

### Where it is going

1. **One qubit in time.** It evolves without losing probability, and the measurement probabilities add up to 1. Done.
2. **Several qubits together.** Two systems combine into one, and the order in which three are grouped does not matter. Done.
3. **The observer inside.** Measurement used to be an _axiom_: the model was told from outside what an observation returns. Now a second qubit, an _apparatus_, interacts with the system through a `CNOT` gate, and the rest is proved. Done:
   - the interaction entangles system and apparatus: their joint state is no longer two separate states;
   - the apparatus reads exactly the probabilities the axiom assumed, and the system, seen alone, loses its coherence;
   - two apparatuses on the same system never disagree, whatever the order in which they look;
   - nothing done to an apparatus changes what the system does.

   What this settles and what it does not is in [`researches/osservatore.md`](researches/osservatore.md).

4. **Nothing from outside.** The pieces the model still took for granted are now proved too. Done:
   - the interaction is not a hand-written gate: it comes from a Hamiltonian, and `CNOT` is one of its points;
   - measurement comes in degrees, from no coupling to a perfect one;
   - reading the apparatus updates the system by the textbook rule, and a second reading repeats the first;
   - energy is conserved, two steps of time make one step, and a change of basis gives the same universe.

The model does not simulate our universe, and it does not try to. It is a laboratory where the parts of a physical theory can be made exact one at a time.

### Glossary

| Term            | Meaning here                                                                                         |
| --------------- | ---------------------------------------------------------------------------------------------------- |
| qubit           | the simplest quantum system: two amplitudes `α`, `β`, with `\|α\|² + \|β\|²` the total probability   |
| `X`, `Φ`, `Obs` | the states, the law of motion, the observation                                                       |
| `U`             | one step of the law of motion, a 2×2 complex matrix                                                  |
| `c`, `s`        | the cosine and sine of the rotation angle, kept as symbols with `c² + s² = 1`                        |
| `n`             | the rotation axis, a unit vector                                                                     |
| Born weight     | the probability of an outcome, the squared modulus of an amplitude                                   |
| entanglement    | a state of two systems that cannot be written as one state for each                                  |
| apparatus       | a qubit that interacts with the system and records it                                                |
| partial trace   | the state of one part of a composite system, with the other part ignored                             |
| decoherence     | the loss of the off-diagonal terms of that state once the system is recorded                         |
| purity          | `1` for a state known exactly, below `1` for a mixture                                               |
| free ring       | polynomials with no rule imposed: an identity there holds for every value of the symbols             |
| `gC`, `gN`      | the two rules `c² + s² − 1` and `nx² + ny² + nz² − 1`                                                |
| `gA`            | the rule that the amplitudes are normalized, `\|α\|² + \|β\|² − 1`                                   |
| `δ`             | the single defect `gC + s² gN` that pays for unitarity                                               |
| ideal           | everything that vanishes once some rules hold; "in the ideal `(gC, gN)`" means "zero on the circle"  |
| cofactors       | the receipt of a proof: they show exactly how an identity follows from the rules                     |
| `3/5`, `4/5`    | a rational point on the circle, the 3-4-5 triangle, where every prediction becomes an exact fraction |

## Getting started

Requirements: Python 3.11 or later, and Lean 4 through [elan](https://github.com/leanprover/elan) (the version is pinned in `lean-toolchain`). There are no other dependencies: no Mathlib, no numerical libraries.

```sh
pip install -e . --group dev   # pytest and the pinned ruff (pip ≥ 25.1)
python -m universe        # the Python certificate
lake build                # the Lean proofs
./check.sh                # every gate, as in CI
```

`python -m universe` exits 0 only when every algebraic identity has remainder zero and the free-ring cofactors rebuild the original polynomial. It prints 54 lines, each marked `[dimostrato]`. `lake build` typechecks the library `Universe`.

`./check.sh` runs ruff, the unit tests in `tests/`, the certificate and `lake build`. Two tests guard the documentation: `tests/test_lean_citations.py` fails when Python or the docs cite a `Universe.*` name that Lean does not declare, `tests/test_doc_counts.py` fails when a doc quotes the wrong number of certificate lines, and `tests/test_lean_map.py` fails unless every certificate line is mapped, in `universe/lean_map.py`, to Lean theorems that exist. GitHub Actions runs the same gates on every push, plus a prettier check of the Markdown.

## Repository layout

| Path              | Content                                                                                                                                                                       |
| ----------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `universe/`       | the Python certificate: `ring.py` (exact scalars, quotient, cofactors), `ontology.py`, `dynamics.py`, `epistemology.py`, `observer.py`, `interaction.py`, `proofs.py`         |
| `Universe/`       | the Lean library, one module per layer: `Ring`, `Quotient`, `Series`, `Dynamics`, `Qubit`, `Epistemology`, `Evaluation`, `Composition`, `Observer`, `Symmetry`, `Interaction` |
| `tests/`          | unit tests of the Python side and the documentation guards                                                                                                                    |
| `papers/qubit.md` | the formal note: which identity lives in which ideal                                                                                                                          |
| `papers/figures/` | the figures, hand-written SVG                                                                                                                                                 |
| `researches/`     | arguments behind single results                                                                                                                                               |
| `plans/`          | executed work plans                                                                                                                                                           |

The README is in English. The notes in `papers/` and `researches/`, the docstrings and the certificate output are in Italian.

## How the proofs work

The universe is the triple `(X, Φ, Obs)`. `X` is a finite-dimensional state space. `Φ` is `exp(−i φ n·σ)`, written in closed form as `U = c I − i s H` with `H = n·σ`; `c` and `s` stay symbols, bound only by `c² + s² = 1` and `|n| = 1`. `expCoeff_hamiltonian` is what licenses that closed form: `H² = I`, so the series of `exp` collapses to cosine and sine. Two representations are the same universe when an isomorphism commutes with `Φ` and `Obs`.

A statement is a polynomial identity. It is proved when its left side minus its right side reduces to zero under the rules, and the proof keeps the **cofactors**: the free-ring expansion `p = Σ fᵢ gᵢ` that rebuilds the polynomial from the rules. Python exhibits those cofactors and checks the expansion. Lean proves the same identities for every polynomial over a monomial of fifteen named exponents (`c s nx ny nz` for the law, eight for the amplitudes of two qubits, `c2 s2` for a second time step), and `Universe.Dynamics.reduce_complete` is the converse: membership in `(gC, gN)` means every coefficient of the remainder is zero. Cofactors are a witness, and they are not unique. Neither certificate is extracted from the other.

The statements separate by the rules they need:

- **free ring**, no rule: `H† = H`, `|z|² = re(z)² + im(z)²`, `⟨ψ|Π₀|ψ⟩ = |α|²`, the tensor identities, `CNOT² = I`, decoherence, the apparatus reading the Born weights, two observers agreeing;
- **`(gC, gN)`**, the circle and the axis, one defect `δ = gC + s² gN`: `U†U = I`, `UU† = I`, `det U = 1`, norm preservation, `P(0) + P(1) = 1` on evolved `|0⟩`, no-signalling;
- **`(gC, gN, gA)`**, adding normalized amplitudes: `P(0) + P(1) = 1` on a generic state, and `1 − purity = 2|α|²|β|²` after the apparatus records the system.

The rational point `c = 3/5`, `s = 4/5`, `n = eₓ` turns those polynomials into fractions: `δ` evaluates to zero there, and `9/25`, `16/25` are the squares of `3/5`, `4/5`.

## One qubit

`U†U − I`, `UU† − I` and `det U − 1` lie in `(gC, gN)` with the same cofactors `gC + s² gN`. `literal_sandwich` gives the literal modulus `‖Uψ‖²` and the sandwich `ψ†(U†U)ψ` the same coefficients for every matrix, so `literal_evolution_norm` and `literal_sphere` carry the ideal memberships onto `‖Uψ‖² − ‖ψ‖²` and `‖Uψ‖² − 1`. Python reduces those polynomials, and the sphere line uses `certify_extra` to add `gA` next to the two rules of the ring.

`keepX` and `keepZ` specialize the axis; `specX_pmul` and `specZ_pmul` make that a ring homomorphism. Along x the coefficients of `gN` vanish and the circle remains: `P(0) = 1 − s²`, `P(1) = s²`. Along z, `|0⟩` is an eigenstate: the second amplitude is the zero polynomial and `P(0) = 1`.

![The circle and the point 3/5, 4/5](papers/figures/cerchio.svg)

| reading                  | P(0)   | P(1)  |
| ------------------------ | ------ | ----- |
| along x                  | 1 − s² | s²    |
| along z                  | 1      | 0     |
| c = 3/5, s = 4/5, n = eₓ | 9/25   | 16/25 |

**Energy is conserved.** `U = c I − i s H` commutes with `H` already in the free ring, since `UH` and `HU` are both `c H − i s H²` (`evolution_commutes_hamiltonian`). So `U†HU = U†UH`, and `⟨Uψ|H|Uψ⟩ − ⟨ψ|H|ψ⟩` lies in `(gC, gN)` for every amplitude (`energy_conserved`). At the rational point `⟨0|H|0⟩` is `0` along x and `1` along z, before and after the evolution.

**Time composes.** Two steps of the law are one step: `U(c₁, s₁) U(c₂, s₂) = U(c₁c₂ − s₁s₂, s₁c₂ + c₁s₂)` modulo `gN` alone (`evolution_compose`). The group law does not use the circle; staying on it does, with `c² + s² − 1 = (c₂² + s₂²) gC₁ + gC₂` (`compose_circle`). `(3/5, 4/5)` composed with itself is `(−7/25, 24/25)`, and `U²|0⟩ = −7/25 |0⟩ − 24/25 i |1⟩`, evaluated in Lean by `evalAt2`, which also reads `c2 s2` (`point_compose`).

![Time composes: the point (3/5, 4/5) twice is (−7/25, 24/25)](papers/figures/tempo.svg)

**A change of basis is the same universe.** For any matrix `V` with `V†V = I`, `V(Uψ)` equals `(VUV†)(Vψ)` (`conj_evolution`), and the Born weights of `Vψ` in the basis `V|k⟩` equal those of `ψ` (`conj_born`): the rotated description evolves and observes exactly like the original, which is the identity principle of the kernel. With `V†V = I` modulo `(gC, gN)` the same holds modulo the ideal (`conj_evolution_rel`, `conj_born_rel`), so it applies to the symbolic law itself, `V = U` (`conj_evolution_law`, `conj_born_law`). At the rational point, `V(U|0⟩) = −7/25 |0⟩ − 24/25 i |1⟩` (`point_conj_evolution`).

## Several qubits

The cell of `|i⟩ ⊗ |k⟩` is `2·i + k`. `kronecker_ui_gen` is `(U ⊗ I)(|ψ⟩ ⊗ |φ⟩) = (U|ψ⟩) ⊗ |φ⟩` for every second factor, and `marginal_left_gen` multiplies the Born weights by `‖φ‖²`; on a generic factor that scale is removed by the cofactor of `gA`. Python compares the case `|φ⟩ = |0⟩`, where the scale is the constant `1`.

Three qubits can be grouped two ways. `tensor_assoc` says the two groupings are the same eight amplitudes, and `tensor_assoc_ui` and `tensor_assoc_ui_right` say that evolving the first factor commutes with the grouping. `tensor_assoc_obs` gives the two groupings the same Born weights.

![The two parenthesizations and U on the first factor](papers/figures/quadrato.svg)

The cell of `|i⟩ ⊗ |j⟩ ⊗ |k⟩` is `4·i + 2·j + k`, in both constructions:

| cell | i   | j   | k   | amplitude |
| ---- | --- | --- | --- | --------- |
| 0    | 0   | 0   | 0   | ψ₀ φ₀ χ₀  |
| 1    | 0   | 0   | 1   | ψ₀ φ₀ χ₁  |
| 2    | 0   | 1   | 0   | ψ₀ φ₁ χ₀  |
| 3    | 0   | 1   | 1   | ψ₀ φ₁ χ₁  |
| 4    | 1   | 0   | 0   | ψ₁ φ₀ χ₀  |
| 5    | 1   | 0   | 1   | ψ₁ φ₀ χ₁  |
| 6    | 1   | 1   | 0   | ψ₁ φ₁ χ₀  |
| 7    | 1   | 1   | 1   | ψ₁ φ₁ χ₁  |

Three copies of evolved `|0⟩` at the rational point fill the eight cells: each bit `0` contributes `9/25`, each bit `1` contributes `16/25`, and the eight weights sum to 1.

![Eight cells of three copies of evolved ground state](papers/figures/celle.svg)

## The observer inside

**Entanglement.** `CNOT` swaps the cells `|10⟩` and `|11⟩`. On `|ψ⟩ ⊗ |0⟩` it gives `α|00⟩ + β|11⟩`. The determinant `a₀a₃ − a₁a₂` of every product state is the zero polynomial (`product_det`); after `CNOT` it is `α β`, which at the rational point is `−12/25 i`. So `CNOT(Φ|0⟩ ⊗ |0⟩)` is not a product (`point_not_product`).

![CNOT couples the system to an apparatus: before it the amplitude grid is a product, after it the state is entangled](papers/figures/cnot.svg)

**The interaction is a dynamics.** `CNOT` is not posited: it comes from the interaction Hamiltonian `G = |1⟩⟨1| ⊗ (n·σ)`. `G` is not an involution, but `G³ = G` (`generator_cube`), and `expCoeff_idem` collapses `exp(−iφ a)` for any such `a` to `(1 − a²) + cos φ · a² − i sin φ · a`. On `G` that is the controlled evolution `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` (`controlled_from_hamiltonian`). At the rational point `c = 0`, `s = 1`, `n = eₓ`, `U = −i X`, and the controlled evolution is `CNOT` up to a local phase (`cnot_point`); the phase drops out of every Born weight, so everything below holds unchanged (`cnot_point_born`).

**Decoherence and the pointer.** `reduceLeft` is the partial trace over the apparatus. Before `CNOT` the system keeps the coherence `α β̄`. After `CNOT` both off-diagonals are the zero polynomial and the diagonal is the Born pair (`decoherence`). `pointer_born` reads the same weights on the apparatus, for evolved `Φ|ψ⟩`: the observation is now that theorem, not an axiom. The system's purity drops from 1 to `337/625` at the rational point.

![Decoherence: the system before and after CNOT, and the apparatus reading the Born weights](papers/figures/decoerenza.svg)

**Measurement comes in degrees.** With the controlled evolution as coupling, the system's coherence is multiplied by `conj(⟨0|U|0⟩)`, with `⟨0|U|0⟩ = c − i s nz`, while its Born weights stay put modulo `(gC, gN)` (`partial_coherence`, `partial_diagonal`). Along x, for `ψ = Φ|0⟩` at the rational point, the coherence is `(12/25 i)·c` and the purity `337/625 + (288/625)·c²` (`partial_reading`): from no coupling to full measurement, `1`, `11017/15625`, `337/625`.

![Partial measurement: the coupling comes from a Hamiltonian, and its angle sets how much the system decoheres](papers/figures/misura-parziale.svg)

**Reading the pointer.** What is the system after the apparatus has been read? Projecting the apparatus on `|k⟩` (`condition`) leaves `(α, 0)` for `k = 0` and `(0, β)` for `k = 1`, with norms equal to the Born pair (`luders`). The update rule, the textbook "collapse", is a theorem here. A second apparatus coupled to the conditioned system reads the same outcome with the same weight and the other with weight zero (`repeatable`).

**Two observers.** With a second apparatus, either order of the two `CNOT` gates gives `α|000⟩ + β|111⟩`. The Born weight of every cell where the two pointers differ is the zero polynomial (`observers_agree`).

![Two apparatuses on the same system: only 000 and 111 occur, so A and B never disagree](papers/figures/osservatori.svg)

**No signalling.** Evolving the apparatus alone leaves every Born weight of the system unchanged, modulo `(gC, gN)`, for every two-qubit state: each of the system's blocks evolves like one qubit, so the difference is `‖Uγ‖² − ‖γ‖²` (`no_signalling_any_0`, `no_signalling_any_1`). The apparatus's own weights do change.

![No signalling: the system's weights stay 9/25 and 16/25 while the apparatus's change](papers/figures/segnale.svg)

## What is proved

Every row is a line of the certificate, a Lean theorem, or both. "certificate" means `python -m universe`.

### Ring

| Fact                                                | Python                                        | Lean                                                                  |
| --------------------------------------------------- | --------------------------------------------- | --------------------------------------------------------------------- |
| Gauss arithmetic, `i² = −1`                         | `universe.ring.Gauss`                         | `Universe.Ring`                                                       |
| Quotient `c² + s² = 1`, `\|n\| = 1`, with cofactors | `reduce_witness`, driven by `Ring.set_square` | `Universe.Quotient.reduce_sound`, `Universe.Dynamics.reduce_complete` |
| Evaluation respects coefficients and products       | `Poly.evaluate`                               | `Universe.Evaluation.eval_polySame`, `Universe.Evaluation.eval_pmul`  |

### Law

| Fact                                                                           | Python                                   | Lean                                                                                                                                                                                                                                                          |
| ------------------------------------------------------------------------------ | ---------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `exp(−i φ a) = cos φ · 1 + (−i sin φ) · a` when `a² = 1`                       | cited                                    | `Universe.Series.expCoeff`                                                                                                                                                                                                                                    |
| `H = n·σ`, with `Y = [[0, −i], [i, 0]]`                                        | `universe.dynamics.pauli`                | `Universe.Qubit.hamiltonian_pauli`                                                                                                                                                                                                                            |
| `H† = H` in the free ring                                                      | certificate                              | `Universe.Qubit.hamiltonian_dagger`                                                                                                                                                                                                                           |
| `H² = I`, `H³ = H`, `H⁴ = I` in the quotient                                   | certificate                              | `Universe.Qubit.hamiltonian_sq`, `Universe.Qubit.hamiltonian_cube`, `Universe.Qubit.hamiltonian_fourth`                                                                                                                                                       |
| The collapse of the series on `H`                                              | closed form                              | `Universe.Qubit.expCoeff_hamiltonian`                                                                                                                                                                                                                         |
| `U†U − I`, `UU† − I`, `det U − 1`, cofactors `gC + s² gN`                      | certificate                              | `Universe.Qubit.evolution_unitary`, `Universe.Qubit.evolution_unitary_rev`, `Universe.Qubit.evolution_det`                                                                                                                                                    |
| `‖Uψ‖² = ‖ψ‖²` on a generic state                                              | certificate, by `reduce`                 | `Universe.Epistemology.literal_evolution_norm`                                                                                                                                                                                                                |
| `UH = HU` in the free ring; `⟨Uψ\|H\|Uψ⟩ = ⟨ψ\|H\|ψ⟩` in `(gC, gN)`            | certificate                              | `Universe.Symmetry.evolution_commutes_hamiltonian`, `Universe.Symmetry.energy_conserved`                                                                                                                                                                      |
| A unitary change of basis commutes with `Φ` and `Obs`                          | certificate                              | `Universe.Symmetry.conj_evolution`, `Universe.Symmetry.conj_born`, `Universe.Symmetry.conj_inverse`, `Universe.Symmetry.point_conj_evolution`, `Universe.Symmetry.point_conj_born`, `Universe.Symmetry.conj_evolution_law`, `Universe.Symmetry.conj_born_law` |
| `U(φ₁) U(φ₂) = U(φ₁ + φ₂)` modulo `gN`; the composed angle stays on the circle | certificate                              | `Universe.Symmetry.evolution_compose`, `Universe.Symmetry.compose_circle`, `Universe.Symmetry.point_compose`                                                                                                                                                  |
| `ψ†(U†U)ψ − ‖ψ‖²` in `(gC, gN)`, any amplitudes                                | same coefficients, by `literal_sandwich` | `Universe.Qubit.evolution_norm`                                                                                                                                                                                                                               |

### Observation

| Fact                                                            | Python                                         | Lean                                                                                                            |
| --------------------------------------------------------------- | ---------------------------------------------- | --------------------------------------------------------------------------------------------------------------- |
| `P(0) + P(1) = 1` on evolved `\|0⟩`                             | certificate                                    | `Universe.Epistemology.ground_prob_sum`                                                                         |
| `\|z\|² = re(z)² + im(z)²`, imaginary part zero, any polynomial | certificate                                    | `Universe.Epistemology.modulus_squares`, `Universe.Epistemology.modulus_imag_zero`                              |
| `P(0)` and `P(1)` have rational coefficients                    | certificate                                    | `Universe.Epistemology.columnBorn_real`, `Universe.Epistemology.ground_prob_real`                               |
| `⟨ψ\|Π₀\|ψ⟩ = \|α\|²`, `Π₀ = diag(1, 0)`                        | certificate                                    | `Universe.Epistemology.projector_born`                                                                          |
| `‖Uψ‖² − 1` in `(gC, gN, gA)` on a generic state                | `certify_extra`                                | `Universe.Epistemology.sphere_prob_sum`, `Universe.Epistemology.literal_sphere`                                 |
| Axis x: `P(0) = 1 − s²`, `P(1) = s²`                            | certificate, substituting the Born polynomials | `Universe.Epistemology.axis_x_born0`, `Universe.Epistemology.axis_x_born1`, `Universe.Epistemology.axis_x_gn`   |
| Axis z: the second amplitude is zero, `P(0) = 1`                | certificate                                    | `Universe.Epistemology.axis_z_born0`, `Universe.Epistemology.axis_z_born1`, `Universe.Epistemology.axis_z_gn`   |
| At the rational point: `P(0) = 9/25`, `P(1) = 16/25`, `δ = 0`   | certificate, numeric matrix and triple tensor  | `Universe.Epistemology.point_prob0`, `Universe.Epistemology.point_prob1`, `Universe.Epistemology.point_unitary` |

### Composition

| Fact                                                                       | Python                                    | Lean                                                                                                                                                       |
| -------------------------------------------------------------------------- | ----------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `\|0⟩ ⊗ \|0⟩ = \|00⟩`                                                      | certificate                               | `Universe.Composition.ground_tensor`                                                                                                                       |
| `(U ⊗ I)(\|ψ⟩ ⊗ \|φ⟩) = (U\|ψ⟩) ⊗ \|φ⟩`, marginal `‖φ‖² · P(U\|ψ⟩)`        | certificate on `\|φ⟩ = \|0⟩`              | `Universe.Composition.kronecker_ui_gen`, `Universe.Composition.marginal_left_gen`                                                                          |
| `(I ⊗ U)(\|ψ⟩ ⊗ \|φ⟩)` has marginal `‖ψ‖² · P(U\|φ⟩)`                      | certificate on `\|ψ⟩ = \|0⟩`              | `Universe.Composition.kronecker_iu_gen`, `Universe.Composition.marginal_right_gen`                                                                         |
| The two groupings of three qubits are the same state, before and after `U` | `tensor_index`, amplitudes, `(U ⊗ I ⊗ I)` | `Universe.Ontology.tensorIndexAssoc`, `Universe.Composition.tensor_assoc`, `Universe.Composition.tensor_assoc_ui`, `Universe.Composition.tensor_assoc_obs` |

### Observer

| Fact                                                                                                                 | Python                               | Lean                                                                                                                                                                                                  |
| -------------------------------------------------------------------------------------------------------------------- | ------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `G³ = G`; `exp(−iφ G)` is the controlled evolution; at `c = 0, s = 1, n = eₓ` it is `CNOT` up to a phase             | certificate                          | `Universe.Series.expCoeff_idem`, `Universe.Interaction.generator_cube`, `Universe.Interaction.controlled_from_hamiltonian`, `Universe.Interaction.cnot_point`, `Universe.Interaction.cnot_point_born` |
| Partial coupling: coherence times `conj(⟨0\|U\|0⟩)`, Born weights unchanged; purity `337/625 + (288/625) c²` along x | certificate                          | `Universe.Interaction.partial_coherence`, `Universe.Interaction.partial_diagonal`, `Universe.Interaction.partial_reading`                                                                             |
| `CNOT² = I`, `‖CNOT v‖² = ‖v‖²`                                                                                      | certificate                          | `Universe.Observer.cnot_involutive`, `Universe.Observer.cnot_norm`                                                                                                                                    |
| A product has determinant zero; `CNOT(Φ\|0⟩ ⊗ \|0⟩)` has `−12/25 i`                                                  | certificate                          | `Universe.Observer.product_det`, `Universe.Observer.point_entangled`, `Universe.Observer.point_not_product`                                                                                           |
| After `CNOT` the reduced system is diagonal with the Born pair                                                       | certificate                          | `Universe.Observer.decoherence`, `Universe.Observer.coherence_before`                                                                                                                                 |
| The apparatus reads `P(Φ\|ψ⟩)`                                                                                       | certificate                          | `Universe.Observer.pointer_born`                                                                                                                                                                      |
| Purity `337/625` at the rational point                                                                               | certificate                          | `Universe.Observer.point_purity`, `Universe.Observer.purity_after`                                                                                                                                    |
| Reduced diagonal = marginal; a product reduces to `‖φ‖² \|ψ⟩⟨ψ\|`; `1 − purity − 2\|α\|²\|β\|²` in `(gA)`            | Lean only                            | `Universe.Observer.reduceLeft_diag`, `Universe.Observer.reduce_product`, `Universe.Observer.purity_before`, `Universe.Observer.purity_sphere`                                                         |
| Two apparatuses never disagree, in either order                                                                      | certificate                          | `Universe.Observer.two_pointers`, `Universe.Observer.observers_agree`, `Universe.Observer.order_irrelevant`                                                                                           |
| Reading the pointer leaves `(α, 0)` or `(0, β)`, with the Born weights; a second reading repeats it                  | certificate                          | `Universe.Composition.condition_norm`, `Universe.Interaction.luders`, `Universe.Interaction.repeatable`, `Universe.Interaction.point_luders`, `Universe.Interaction.point_repeatable`                 |
| Evolving the apparatus leaves the system's weights unchanged, any two-qubit state                                    | certificate, generic two-qubit state | `Universe.Observer.no_signalling_any_0`, `Universe.Observer.no_signalling_any_1`, `Universe.Observer.no_signalling_gen_0`, `Universe.Observer.no_signalling_gen_1`                                    |

## Further reading

- [`papers/qubit.md`](papers/qubit.md): the formal note, section by section, with the ideal of each identity.
- [`researches/divisione-monica.md`](researches/divisione-monica.md): the monic division behind `reduce_complete`.
- [`researches/associazione.md`](researches/associazione.md): the three-qubit associativity.
- [`researches/osservatore.md`](researches/osservatore.md): what the observer construction settles, and what it does not.
- [`researches/monomio.md`](researches/monomio.md): why the Lean monomial keeps named exponents instead of a parameter.
- [`plans/observer-inside.md`](plans/observer-inside.md): the plan that built the observer, phase by phase.
- [`plans/parametric-mono.md`](plans/parametric-mono.md): a wider Lean monomial.
- [`plans/no-outside.md`](plans/no-outside.md): removing what the model still takes from outside: the interaction, perfect measurement, time composition, conservation, change of basis.

## License

[MIT](LICENSE).
