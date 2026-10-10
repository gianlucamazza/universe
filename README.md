# universe

Exact kernel of one universe: the triple `(X, Φ, Obs)`. The first world is a qubit.

`X` is a finite-dimensional state space. `Φ` is `exp(-i φ n·σ)`, packaged as the closed form `U = c I − i s H` on the quotient `c² + s² = 1`, `|n| = 1`. `Obs` is the computational-basis measurement. Two representations are the same universe when an isomorphism commutes with `Φ` and `Obs`.

The Python package is the executable certificate. Lean 4 is the formal one. Both rewrite `c²` and `nx²` and keep the cofactors. Neither is an extraction of the other. The note that records how the identities split is [`papers/qubit.md`](papers/qubit.md). The monic division behind `reduce_complete` is [`researches/divisione-monica.md`](researches/divisione-monica.md). The three-qubit associativity is [`researches/associazione.md`](researches/associazione.md).

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

The two parenthesizations of three qubits are the same encoded state. The square, the eight cells, and the two rings of the certificate are drawn under Representations. The line remains one of the 24.

`Universe.Dynamics.reduce_complete` is the converse for this `reduce`: membership in `(gC, gN)` means every coefficient of the remainder is zero. The statement is on `coeffOf`. Cofactors are a witness, and they are not unique. The rational point is the 3-4-5 triangle on the circle, so `9/25` and `16/25` are the squares of `3/5` and `4/5`. Those coefficients show which generator pays for which identity.

## Representations

The two parenthesizations are one encoded state. Association and then `U` on the first factor is the same list as `U` and then association.

```mermaid
flowchart LR
  L["tensorLeft (ψ, φ, χ)"]
  R["tensorRight (ψ, φ, χ)"]
  LU["tensorLeft (Uψ, φ, χ)"]
  RU["tensorRight (Uψ, φ, χ)"]
  L -->|tensor_assoc| R
  L -->|tensor_assoc_ui| LU
  R -->|tensor_assoc_ui_right| RU
  LU -->|tensor_assoc| RU
```

`tensor_assoc_obs` equates `z · conj(z)` on each cell of the two states before `U`. The two states after `U` have the same weights because those states are equal.

The cell of `|i⟩ ⊗ |j⟩ ⊗ |k⟩` is `4·i + 2·j + k`. Both constructions fill the same table. `applyUII` uses the first row of `U` on cells `0`–`3` and the second row on cells `4`–`7`.

| cell | i | j | k | amplitude |
|---|---|---|---|---|
| 0 | 0 | 0 | 0 | ψ₀ φ₀ χ₀ |
| 1 | 0 | 0 | 1 | ψ₀ φ₀ χ₁ |
| 2 | 0 | 1 | 0 | ψ₀ φ₁ χ₀ |
| 3 | 0 | 1 | 1 | ψ₀ φ₁ χ₁ |
| 4 | 1 | 0 | 0 | ψ₁ φ₀ χ₀ |
| 5 | 1 | 0 | 1 | ψ₁ φ₀ χ₁ |
| 6 | 1 | 1 | 0 | ψ₁ φ₁ χ₀ |
| 7 | 1 | 1 | 1 | ψ₁ φ₁ χ₁ |

The index identity of the certificate lives on the ring `(i, j, k, nb, nc)`. The amplitudes and `(U ⊗ I ⊗ I)` live on `(u00, u01, u10, u11, a0, a1, b0, b1, c0, c1)`. The three writings `(U ⊗ I) ⊗ I`, `U ⊗ (I ⊗ I)` and `U ⊗ I₄` meet the factored state. Lean states the same identities for every polynomial. The printed detail cites `tensor_assoc`, `tensor_assoc_ui` and `tensor_assoc_obs`.

On the circle, the rational point is the 3-4-5 triangle. `δ` evaluates to zero there. `9/25` and `16/25` are the squares of `3/5` and `4/5`.

| reading | P(0) | P(1) |
|---|---|---|
| along x | 1 − s² | s² |
| along z | 1 | 0 |
| c = 3/5, s = 4/5, n = e_x | 9/25 | 16/25 |

## What is proved

| Layer | Fact | Python | Lean |
|---|---|---|---|
| Ring | Gauss arithmetic, `i² = -1` | `universe.ring.Gauss` | `Universe.Ring` |
| Ring | Quotient `c² + s² = 1`, `\|n\| = 1`, with cofactors | `reduce_witness`, driven by `Ring.set_square` | `Universe.Quotient.reduce_sound`, `Universe.Dynamics.reduce_complete` |
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
| Composition | Two parenthesizations of three qubits are the same state | `tensor_index`, amplitudes, `(U⊗I⊗I)` | `tensorIndexAssoc`, `tensor_assoc`, `tensor_assoc_ui`, `tensor_assoc_obs` |
| Composition | `\|0⟩ ⊗ \|0⟩ = \|00⟩`, amplitude `1` in cell 0 | certificate | `Universe.Composition.ground_tensor` |
| Composition | `(U ⊗ I)(\|ψ⟩ ⊗ \|φ⟩) = (U\|ψ⟩) ⊗ \|φ⟩`, marginal `‖φ‖² · P(U\|ψ⟩)` | certificate on `\|φ⟩ = \|0⟩`; `\|00⟩` is `α = 1`, `β = 0` | `kronecker_ui_gen`, `marginal_left_gen` |
| Composition | `(I ⊗ U)(\|ψ⟩ ⊗ \|φ⟩)` has marginal `‖ψ‖² · P(U\|φ⟩)` | certificate on `\|ψ⟩ = \|0⟩`, same reading | `kronecker_iu_gen`, `marginal_right_gen` |
