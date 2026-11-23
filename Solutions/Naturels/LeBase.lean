/- @parcours
titre: Premiers pas avec ≤
difficulte: 2
indice: `le_refl` : `exact ⟨0, rfl⟩` (car `a = a + 0`).
indice: `zero_le` : `exact ⟨a, (zero_add a).symm⟩`.
indice: `le_trans` : `obtain ⟨x, hx⟩ := hab`, `obtain ⟨y, hy⟩ := hbc`, puis `exact ⟨x + y, by rw [hy, hx, add_assoc]⟩`.
-/
import Solutions.Naturels.Ordre
import Solutions.Naturels.AddAssoc
import Solutions.Naturels.ZeroAdd

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
-/

namespace Parcours.ℕ

theorem le_refl (a : ℕ) : a ≤ a := by -- @exo
  exact ⟨0, rfl⟩

theorem zero_le (a : ℕ) : 0 ≤ a := by -- @exo
  exact ⟨a, (zero_add a).symm⟩

theorem le_succ_self (a : ℕ) : a ≤ succ a := by -- @exo
  exact ⟨1, rfl⟩

theorem le_trans (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by -- @exo
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  exact ⟨x + y, by rw [hy, hx, add_assoc]⟩

end Parcours.ℕ

#verifier
