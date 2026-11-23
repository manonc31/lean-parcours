import Exercices.Naturels.MulAdd

/-!
# Associativité de la multiplication

## À prouver
`mul_assoc (a b c : ℕ) : a * b * c = a * (b * c)`

---
*Exercice* `Naturels.MulAssoc` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.MulAssoc` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := by
  sorry

end Parcours.ℕ

#verifier
