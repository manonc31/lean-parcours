import Exercices.Naturels.PowAdd
import Exercices.Naturels.AddMul

/-!
# Puissances de produits

## À prouver
1. `mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n`
2. `pow_mul (a m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n`

---
*Exercice* `Naturels.PowMul` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.PowMul` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  sorry

theorem pow_mul (a m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := by
  sorry

end Parcours.ℕ

#verifier
