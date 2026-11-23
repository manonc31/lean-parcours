import Exercices.Matrices.Definitions

/-!
# Le produit est associatif

Le produit de matrices est **associatif** : `(AB)C = A(BC)`. (Mais pas commutatif, voir l'exercice suivant !)

## À prouver
1. `mul_assoc : A * B * C = A * (B * C)`
2. `id_mul : id2 * A = A` et `mul_id : A * id2 = A`

---
*Exercice* `Matrices.Associativite` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Matrices.Associativite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Matrices

theorem mul_assoc (A B C : M2) : A * B * C = A * (B * C) := by
  sorry

theorem id_mul (A : M2) : M2.id2 * A = A := by
  sorry

theorem mul_id (A : M2) : A * M2.id2 = A := by
  sorry

end Parcours.Matrices

#verifier
