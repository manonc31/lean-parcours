import Exercices.Matrices.Definitions

/-!
# Le produit n'est pas commutatif

Contrairement aux nombres, `AB ≠ BA` en général ! Trouve deux matrices qui ne commutent pas.

## À prouver
`non_commutatif : ∃ A B : M2, A * B ≠ B * A`

---
*Exercice* `Matrices.NonCommutatif` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Matrices.NonCommutatif` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Matrices

theorem non_commutatif : ∃ A B : M2, A * B ≠ B * A := by
  sorry

end Parcours.Matrices

#verifier
