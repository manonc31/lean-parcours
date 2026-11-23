import Exercices.Naturels.LeBase
import Exercices.Naturels.Simplification
import Exercices.Naturels.SuccAdd

/-!
# L'ordre et l'addition

## À prouver
1. `add_le_add_left (a b c : ℕ) : a ≤ b → c + a ≤ c + b`
2. `le_of_add_le_add_left (a b c : ℕ) : c + a ≤ c + b → a ≤ b`
3. `succ_le_succ (a b : ℕ) : a ≤ b → succ a ≤ succ b`
4. `le_of_succ_le_succ (a b : ℕ) : succ a ≤ succ b → a ≤ b`

---
*Exercice* `Naturels.LeAdd` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.LeAdd` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem add_le_add_left (a b c : ℕ) (h : a ≤ b) : c + a ≤ c + b := by
  sorry

theorem le_of_add_le_add_left (a b c : ℕ) (h : c + a ≤ c + b) : a ≤ b := by
  sorry

theorem succ_le_succ (a b : ℕ) (h : a ≤ b) : succ a ≤ succ b := by
  sorry

theorem le_of_succ_le_succ (a b : ℕ) (h : succ a ≤ succ b) : a ≤ b := by
  sorry

end Parcours.ℕ

#verifier
