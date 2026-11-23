import Exercices.Naturels.LeAntisymm
import Exercices.Naturels.LeAdd

/-!
# L'ordre strict

Rappel : `a < b` est défini comme `succ a ≤ b`.

## À prouver
1. `lt_irrefl (a : ℕ) : ¬a < a`
2. `lt_iff_le_ne (a b : ℕ) : a < b ↔ a ≤ b ∧ a ≠ b`
3. `zero_lt_succ (n : ℕ) : 0 < succ n`
4. `not_lt_zero (a : ℕ) : ¬a < 0`

---
*Exercice* `Naturels.Strict` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.Strict` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem lt_irrefl (a : ℕ) : ¬a < a := by
  sorry

theorem lt_iff_le_ne (a b : ℕ) : a < b ↔ a ≤ b ∧ a ≠ b := by
  sorry

theorem zero_lt_succ (n : ℕ) : 0 < succ n := by
  sorry

theorem not_lt_zero (a : ℕ) : ¬a < 0 := by
  sorry

end Parcours.ℕ

#verifier
