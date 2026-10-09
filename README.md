# universe

Exact kernel of one universe: the triple `(X, Φ, Obs)`. The first world is a qubit.

`X` is a finite-dimensional state space. `Φ` is `exp(-i φ n·σ)`, packaged as the closed form `U = c I − i s H` on the quotient `c² + s² = 1`, `|n| = 1`. `Obs` is the computational-basis measurement. Two representations are the same universe when an isomorphism commutes with `Φ` and `Obs`.

The Python package is the executable certificate. Lean 4 is the formal one. They implement the same reductions; neither is an extraction of the other.

## Run

```sh
python -m universe
lake build
```

`python -m universe` exits 0 only when every algebraic identity has remainder zero and the free-ring cofactors rebuild the original polynomial. `lake build` typechecks the default target, including `Universe.Qubit`.

## What is proved

| Fact | Python | Lean |
|---|---|---|
| Gauss arithmetic, `i² = -1` | `universe.ring.Gauss` | `Universe.Ring` |
| Quotient `c² + s² = 1`, `\|n\| = 1`, with cofactors | `reduce_witness`, driven by `Ring.set_square` | `Universe.Quotient.reduce_sound` |
| `exp(-i φ a) = cos φ · 1 + (-i sin φ) · a` when `a² = 1` | cited | `Universe.Series.expCoeff` |
| That instance on `H`, because `H² = I` in the quotient | `H² = I` certificate | `Universe.Qubit.expCoeff_hamiltonian` |
| `U†U = I` | certificate | `Universe.Qubit.evolution_unitary` |
| Amplitude sphere `ar² + ai² + br² + bi² = 1` | `Poly.certify_extra` | `gA`, `Universe.Qubit.evolved_on_sphere` |
| Tensor index associativity | `tensor_index` | `Universe.Ontology.tensorIndexAssoc` |

`c` and `s` stay indeterminates of the circle quotient. They are not the cosine and sine series. `expCoeff_hamiltonian` is what licenses writing `U` as that closed form.
