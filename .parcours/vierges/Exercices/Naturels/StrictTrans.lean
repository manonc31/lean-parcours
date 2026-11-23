import Exercices.Naturels.LeBase

/-!
# Transitivité de <

Rappel : `a < b` signifie `succ a ≤ b`.

## À prouver
1. `lt_succ_self : a < succ a`
2. `lt_of_lt_of_le : a < b → b ≤ c → a < c`
3. `lt_trans : a < b → b < c → a < c`

---
*Exercice* `Naturels.StrictTrans` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.StrictTrans` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem lt_succ_self (a : ℕ) : a < succ a := by
  sorry

theorem lt_of_lt_of_le {a b c : ℕ} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  sorry

theorem lt_trans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  sorry

end Parcours.ℕ

#verifier
