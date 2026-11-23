/- @parcours
titre: Transitivité de <
difficulte: 2
requiert: Naturels.Strict
indice: `a < succ a` signifie `succ a ≤ succ a` : `le_refl`.
indice: Pour `lt_trans` : `succ a ≤ b ≤ succ b ≤ c` (`le_succ_self`, `le_trans`).
-/
import Solutions.Naturels.LeBase

/-!
# Transitivité de <

Rappel : `a < b` signifie `succ a ≤ b`.

## À prouver
1. `lt_succ_self : a < succ a`
2. `lt_of_lt_of_le : a < b → b ≤ c → a < c`
3. `lt_trans : a < b → b < c → a < c`
-/

namespace Parcours.ℕ

theorem lt_succ_self (a : ℕ) : a < succ a := by -- @exo
  exact le_refl (succ a)

theorem lt_of_lt_of_le {a b c : ℕ} (h1 : a < b) (h2 : b ≤ c) : a < c := by -- @exo
  exact le_trans _ _ _ h1 h2

theorem lt_trans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by -- @exo
  exact le_trans _ _ _ h1 (le_trans _ _ _ (le_succ_self b) h2)

end Parcours.ℕ

#verifier
