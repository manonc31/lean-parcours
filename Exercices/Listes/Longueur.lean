import Exercices.Listes.Definitions

/-!
# Longueur d'une concaténation

## À prouver
1. `longueur_concat (l₁ l₂ : Liste α) : longueur (l₁ ++ l₂) = longueur l₁ + longueur l₂`
2. `longueur_eq_zero (l : Liste α) : longueur l = 0 ↔ l = nil`

---
*Exercice* `Listes.Longueur` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Listes.Longueur` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α : Type}

theorem longueur_concat (l₁ l₂ : Liste α) : longueur (l₁ ++ l₂) = longueur l₁ + longueur l₂ := by
  sorry

theorem longueur_eq_zero (l : Liste α) : longueur l = 0 ↔ l = nil := by
  sorry

end Parcours.Listes.Liste

#verifier
