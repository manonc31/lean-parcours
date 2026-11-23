import Exercices.Naturels.LeBase
import Exercices.Naturels.SuccAdd

/-!
# L'ordre est total

Deux entiers sont toujours comparables : `a ≤ b` ou `b ≤ a`.

## À prouver
`le_total (a b : ℕ) : a ≤ b ∨ b ≤ a`

---
*Exercice* `Naturels.LeTotal` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.LeTotal` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem le_total (a b : ℕ) : a ≤ b ∨ b ≤ a := by
  sorry

end Parcours.ℕ

#verifier
