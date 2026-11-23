/- @parcours
titre: Ordre et multiplication
difficulte: 2
requiert: Naturels.LeAdd
indice: `le_add_right` : le témoin est `b`, et c'est vrai par définition.
indice: `mul_le_mul_left` : de `b = a + d`, on a `c * b = c * a + c * d` (`mul_add`).
-/
import Solutions.Naturels.LeBase
import Solutions.Naturels.MulAdd

/-!
# Ordre et multiplication

La multiplication respecte l'ordre : si `a ≤ b`, alors `c × a ≤ c × b`.

## À prouver
1. `le_add_right : a ≤ a + b`
2. `mul_le_mul_left : a ≤ b → c * a ≤ c * b`
-/

namespace Parcours.ℕ

theorem le_add_right (a b : ℕ) : a ≤ a + b := by -- @exo
  exact ⟨b, rfl⟩

theorem mul_le_mul_left (a b c : ℕ) (h : a ≤ b) : c * a ≤ c * b := by -- @exo
  obtain ⟨d, rfl⟩ := h
  exact ⟨c * d, mul_add c a d⟩

end Parcours.ℕ

#verifier
