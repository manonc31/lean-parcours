import Exercices.Naturels.PowBase
import Exercices.Naturels.MulAssoc

/-!
# Puissance d'une somme d'exposants

`a^(m+n) = a^m × a^n`.

## À prouver
`pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n`

---
*Exercice* `Naturels.PowAdd` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.PowAdd` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  sorry

end Parcours.ℕ

#verifier
