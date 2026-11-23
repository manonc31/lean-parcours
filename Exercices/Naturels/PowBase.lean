import Exercices.Naturels.Puissance
import Exercices.Naturels.MulBase

/-!
# Premières puissances

## À prouver
1. `zero_pow_succ (n : ℕ) : (0 : ℕ) ^ succ n = 0`
2. `pow_one (a : ℕ) : a ^ (1 : ℕ) = a`
3. `one_pow (n : ℕ) : (1 : ℕ) ^ n = 1`

---
*Exercice* `Naturels.PowBase` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.PowBase` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem zero_pow_succ (n : ℕ) : (0 : ℕ) ^ succ n = 0 := by
  sorry

theorem pow_one (a : ℕ) : a ^ (1 : ℕ) = a := by
  sorry

theorem one_pow (n : ℕ) : (1 : ℕ) ^ n = 1 := by
  sorry

end Parcours.ℕ

#verifier
