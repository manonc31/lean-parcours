import Exercices.Naturels.Multiplication
import Exercices.Naturels.Successeur

/-!
# Multiplier par 0 et par 1

## À prouver
1. `zero_mul (a : ℕ) : 0 * a = 0`
2. `mul_one (a : ℕ) : a * 1 = a`
3. `one_mul (a : ℕ) : 1 * a = a`

## Rappel
`mul_zero a : a * 0 = 0`, `mul_succ a b : a * succ b = a * b + a`, `one_eq_succ_zero`, `succ_eq_add_one`.

---
*Exercice* `Naturels.MulBase` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.MulBase` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem zero_mul (a : ℕ) : 0 * a = 0 := by
  sorry

theorem mul_one (a : ℕ) : a * 1 = a := by
  sorry

theorem one_mul (a : ℕ) : 1 * a = a := by
  sorry

end Parcours.ℕ

#verifier
