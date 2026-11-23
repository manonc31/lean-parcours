import Exercices.Naturels.Multiplication
import Exercices.Naturels.SommeNulle

/-!
# Un produit nul

Si `a × b = 0`, alors `a = 0` ou `b = 0`. (On dit que ℕ est « intègre ».)

## À prouver
`mul_eq_zero (a b : ℕ) : a * b = 0 → a = 0 ∨ b = 0`

---
*Exercice* `Naturels.MulEqZero` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.MulEqZero` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem mul_eq_zero (a b : ℕ) : a * b = 0 → a = 0 ∨ b = 0 := by
  sorry

end Parcours.ℕ

#verifier
