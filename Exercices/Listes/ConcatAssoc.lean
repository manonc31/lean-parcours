import Exercices.Listes.Definitions

/-!
# Associativité de la concaténation

## À prouver
`concat_assoc (l₁ l₂ l₃ : Liste α) : l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃)`

---
*Exercice* `Listes.ConcatAssoc` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Listes.ConcatAssoc` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

theorem concat_assoc {α : Type} (l₁ l₂ l₃ : Liste α) : l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  sorry

end Parcours.Listes.Liste

#verifier
