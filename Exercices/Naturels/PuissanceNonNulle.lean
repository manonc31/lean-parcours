import Exercices.Naturels.PowBase
import Exercices.Naturels.MulEqZero

/-!
# Une puissance non nulle

Si `a ≠ 0`, alors `aⁿ ≠ 0`.

## À prouver
`pow_ne_zero (a n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0`

---
*Exercice* `Naturels.PuissanceNonNulle` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.PuissanceNonNulle` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem pow_ne_zero (a n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by
  sorry

end Parcours.ℕ

#verifier
