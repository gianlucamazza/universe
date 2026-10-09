/-
Ontologia: stati e composizione.

L'indice di `(A ⊗ B) ⊗ C` è `((i * nb + j) * nc + k)`.
La stessa cella in `A ⊗ (B ⊗ C)` è `i * (nb * nc) + (j * nc + k)`.
-/
namespace Universe.Ontology

theorem tensorIndexAssoc (i j k nb nc : Nat) :
    ((i * nb + j) * nc + k) = i * (nb * nc) + (j * nc + k) := by
  simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

end Universe.Ontology
