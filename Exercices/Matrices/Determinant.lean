import Exercices.Matrices.Definitions

/-!
# Le déterminant d'un produit

Le déterminant est **multiplicatif** : `det(AB) = det(A) det(B)`. Géométriquement : le déterminant
mesure comment une matrice multiplie les aires, et faire deux transformations multiplie les facteurs.

## À prouver
1. `det_mul : det (A * B) = det A * det B`
2. `det_id : det id2 = 1`

---
*Exercice* `Matrices.Determinant` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Matrices.Determinant` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Matrices

theorem det_mul (A B : M2) : M2.det (A * B) = M2.det A * M2.det B := by
  sorry

theorem det_id : M2.det M2.id2 = 1 := by
  sorry

end Parcours.Matrices

#verifier
