import Exercices.Naturels.Ordre
import Exercices.Naturels.AddAssoc
import Exercices.Naturels.ZeroAdd

/-!
# Premiers pas avec ≤

Rappel : `a ≤ b` signifie `∃ c, b = a + c`.

Nouveauté : `by …` peut s'utiliser **à l'intérieur** d'un terme, pour prouver un morceau :
`exact ⟨c, by rw [...]⟩`.

## À prouver
1. `le_refl (a : ℕ) : a ≤ a`
2. `zero_le (a : ℕ) : 0 ≤ a`
3. `le_succ_self (a : ℕ) : a ≤ succ a`
4. `le_trans (a b c : ℕ) : a ≤ b → b ≤ c → a ≤ c`

---
*Exercice* `Naturels.LeBase` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.LeBase` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem le_refl (a : ℕ) : a ≤ a := by
  sorry

theorem zero_le (a : ℕ) : 0 ≤ a := by
  sorry

theorem le_succ_self (a : ℕ) : a ≤ succ a := by
  sorry

theorem le_trans (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  sorry

end Parcours.ℕ

#verifier
