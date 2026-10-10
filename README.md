# universe

Exact kernel of one universe: the triple `(X, Φ, Obs)`. The first world is a qubit.

`X` is a finite-dimensional state space. `Φ` is `exp(-i φ n·σ)`, packaged as the closed form `U = c I − i s H` on the quotient `c² + s² = 1`, `|n| = 1`. `Obs` is the computational-basis measurement. Two representations are the same universe when an isomorphism commutes with `Φ` and `Obs`.

The Python package is the executable certificate. Lean 4 is the formal one. Both rewrite `c²` and `nx²` and keep the cofactors. Neither is an extraction of the other. The note that records how the identities split is [`papers/qubit.md`](papers/qubit.md).

## Run

```sh
python -m universe
lake build
```

`python -m universe` exits 0 only when every algebraic identity has remainder zero and the free-ring cofactors rebuild the original polynomial. It prints 24 lines. `lake build` typechecks the library `Universe`.

## Reading

The statements separate by the generators they use.

In the free ring: `H† = H`, `|z|² = re(z)² + im(z)²` with rational coefficients, `⟨ψ|Π₀|ψ⟩ = |α|²`, `|0⟩ ⊗ |0⟩ = |00⟩`, and the Kronecker identities with an idle `|0⟩`.

In the ideal `(gC, gN)`, one defect `δ = gC + s² gN`: `U†U − I`, `UU† − I`, `det U − 1`, norm preservation for arbitrary amplitudes, and `P(0) + P(1) − 1` on evolved `|0⟩`. The amplitudes of `|0⟩` are `1` and `0`.

In the ideal `(gC, gN, gA)`: `ψ†(U†U)ψ − 1` on the generic state `(ar + i ai, br + i bi)`. `gA` is the amplitude sphere. `reduce` still rewrites only `c²` and `nx²`.

`keepX` and `keepZ` specialize an axis. Along x the coefficients of `gN` are zero and the circle remains. Along z the second amplitude is the zero polynomial. The point `c = 3/5`, `s = 4/5`, `n = e_x` evaluates `δ` to zero in `ℚ`.

`literal_sandwich` gives the literal modulus `‖Uψ‖²` and the sandwich `ψ†(U†U)ψ` the same coefficients, for every matrix. `literal_evolution_norm` and `literal_sphere` carry the ideal memberships onto `‖Uψ‖² − ‖ψ‖²` and `‖Uψ‖² − 1`. Python reduces those polynomials, and the sphere line uses `certify_extra`. `specX_pmul` and `specZ_pmul` make specialization a ring homomorphism, so `axis_x_born0`, `axis_x_born1`, `axis_z_born0` and `axis_z_born1` start from `groundP0` and `groundP1`, the polynomials Python substitutes. `axis_z_gn` sends the coefficients of `gN` to zero along z. Lean evaluates `δ` and those weights; Python multiplies the numeric matrix. `kronecker_ui_gen` is `(U ⊗ I)(|ψ⟩ ⊗ |φ⟩) = (U|ψ⟩) ⊗ |φ⟩` for every second factor, and `marginal_left_gen` multiplies the Born weights by `‖φ‖²`. On a generic factor that scale is removed by the cofactor `gA`, outside `reduce`. The `|φ⟩ = |0⟩` case is the constant `1`, which is what Python compares; `|00⟩` is `α = 1`, `β = 0`.

`c` and `s` stay indeterminates of the circle quotient. `expCoeff_hamiltonian` is what licenses writing `U` as that closed form.

## What is proved

| Layer | Fact | Python | Lean |
|---|---|---|---|
| Ring | Gauss arithmetic, `i² = -1` | `universe.ring.Gauss` | `Universe.Ring` |
| Ring | Quotient `c² + s² = 1`, `\|n\| = 1`, with cofactors | `reduce_witness`, driven by `Ring.set_square` | `Universe.Quotient.reduce_sound` |
| Law | `exp(-i φ a) = cos φ · 1 + (-i sin φ) · a` when `a² = 1` | cited | `Universe.Series.expCoeff` |
| Law | `H = n·σ`, with `Y = [[0, −i], [i, 0]]` | `universe.dynamics.pauli` | `Universe.Qubit.hamiltonian_pauli` |
| Law | `H† = H` in the free ring | certificate | `Universe.Qubit.hamiltonian_dagger` |
| Law | `H² = I` in the quotient, diagonal cofactor `gN` | certificate | `Universe.Qubit.hamiltonian_sq` |
| Law | `H³ = H`, from `H² = I` | certificate | `Universe.Qubit.hamiltonian_cube` |
| Law | `H⁴ = I`, from `H² = I` | certificate | `Universe.Qubit.hamiltonian_fourth` |
| Law | That instance on `H` | closed form | `Universe.Qubit.expCoeff_hamiltonian` |
| Law | `U†U − I`, cofactors `gC + s² gN` | certificate | `Universe.Qubit.evolution_unitary` |
| Law | `UU† − I`, same cofactors | certificate | `Universe.Qubit.evolution_unitary_rev` |
| Law | `det U − 1`, same cofactors | certificate | `Universe.Qubit.evolution_det` |
| Law | `‖Uψ‖² = ‖ψ‖²` on a generic state | certificate, by `reduce` | `Universe.Epistemology.literal_evolution_norm` |
| Law | `ψ†(U†U)ψ − ‖ψ‖²` in that ideal, any amplitudes | same coefficients, by `literal_sandwich` | `Universe.Qubit.evolution_norm` |
| Observation | `P(0) + P(1) = 1` on evolved `|0⟩` | certificate | `Universe.Epistemology.ground_prob_sum` |
| Observation | `|z|² = re(z)² + im(z)²`, imaginary part zero, any polynomial | certificate | `Universe.Epistemology.modulus_squares`, `modulus_imag_zero` |
| Observation | `P(0)` and `P(1)` have rational coefficients, any amplitude and `Φ\|0⟩` | certificate | `Universe.Epistemology.columnBorn_real`, `ground_prob_real` |
| Observation | `⟨ψ\|Π₀\|ψ⟩ = \|α\|²`, `Π₀ = diag(1, 0)` | certificate | `Universe.Epistemology.projector_born` |
| Observation | On the generic state, `‖Uψ‖² − 1` in `(gC, gN, gA)` | `certify_extra` | `sphere_prob_sum`, `literal_sphere` |
| Observation | Axis x: `P(0) − (1 − s²) = gC`, `P(1) = s²`, coefficients of `gN` are zero | certificate, substituting the Born polynomials | `axis_x_born0`, `axis_x_born1`, `axis_x_gn` |
| Observation | Axis z: the second amplitude is zero, `P(0) − 1 = gC`, coefficients of `gN` are zero | certificate, reduced `P(0) = 1` | `axis_z_born1`, `axis_z_born0`, `axis_z_gn` |
| Observation | `c = 3/5`, `s = 4/5`, `n = e_x`: `P(0) = 9/25`, `P(1) = 16/25`, `δ` evaluates to 0 | certificate, numeric matrix | `point_prob0`, `point_prob1`, `point_unitary` |
| Composition | Tensor index associativity | `tensor_index` | `Universe.Ontology.tensorIndexAssoc` |
| Composition | `\|0⟩ ⊗ \|0⟩ = \|00⟩`, amplitude `1` in cell 0 | certificate | `Universe.Composition.ground_tensor` |
| Composition | `(U ⊗ I)(\|ψ⟩ ⊗ \|φ⟩) = (U\|ψ⟩) ⊗ \|φ⟩`, marginal `‖φ‖² · P(U\|ψ⟩)` | certificate on `\|φ⟩ = \|0⟩`; `\|00⟩` is `α = 1`, `β = 0` | `kronecker_ui_gen`, `marginal_left_gen` |
| Composition | `(I ⊗ U)(\|ψ⟩ ⊗ \|φ⟩)` has marginal `‖ψ‖² · P(U\|φ⟩)` | certificate on `\|ψ⟩ = \|0⟩`, same reading | `kronecker_iu_gen`, `marginal_right_gen` |
