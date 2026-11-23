/- @parcours
titre: Le déterminant d'un produit
difficulte: 2
requiert: Matrices.Associativite
indice: Déplie tout : `simp only [M2.det, M2.mul_def]`, puis `grind`.
-/
import Solutions.Matrices.Definitions

/-!
# Le déterminant d'un produit

Le déterminant est **multiplicatif** : `det(AB) = det(A) det(B)`. Géométriquement : le déterminant
mesure comment une matrice multiplie les aires, et faire deux transformations multiplie les facteurs.

## À prouver
1. `det_mul : det (A * B) = det A * det B`
2. `det_id : det id2 = 1`
-/

namespace Parcours.Matrices

theorem det_mul (A B : M2) : M2.det (A * B) = M2.det A * M2.det B := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  obtain ⟨e, f, g, h⟩ := B
  simp only [M2.det, M2.mul_def]
  grind

theorem det_id : M2.det M2.id2 = 1 := by -- @exo
  rfl

end Parcours.Matrices

#verifier
