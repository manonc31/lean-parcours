/- @parcours
titre: L'ordre et l'addition
difficulte: 2
indice: `add_le_add_left` : de `b = a + d`, déduis `c + b = (c + a) + d` (`add_assoc`).
indice: `le_of_add_le_add_left` : de `c + b = (c + a) + d`, `add_assoc` puis `add_left_cancel`.
indice: `succ_le_succ` : `succ b = succ a + d` grâce à `succ_add`.
-/
import Solutions.Naturels.LeBase
import Solutions.Naturels.Simplification
import Solutions.Naturels.SuccAdd

/-!
# L'ordre et l'addition

## À prouver
1. `add_le_add_left (a b c : ℕ) : a ≤ b → c + a ≤ c + b`
2. `le_of_add_le_add_left (a b c : ℕ) : c + a ≤ c + b → a ≤ b`
3. `succ_le_succ (a b : ℕ) : a ≤ b → succ a ≤ succ b`
4. `le_of_succ_le_succ (a b : ℕ) : succ a ≤ succ b → a ≤ b`
-/

namespace Parcours.ℕ

theorem add_le_add_left (a b c : ℕ) (h : a ≤ b) : c + a ≤ c + b := by -- @exo
  obtain ⟨d, hd⟩ := h
  exact ⟨d, by rw [hd, add_assoc]⟩

theorem le_of_add_le_add_left (a b c : ℕ) (h : c + a ≤ c + b) : a ≤ b := by -- @exo
  obtain ⟨d, hd⟩ := h
  rw [add_assoc] at hd
  exact ⟨d, add_left_cancel c b (a + d) hd⟩

theorem succ_le_succ (a b : ℕ) (h : a ≤ b) : succ a ≤ succ b := by -- @exo
  obtain ⟨d, hd⟩ := h
  exact ⟨d, by rw [hd, succ_add]⟩

theorem le_of_succ_le_succ (a b : ℕ) (h : succ a ≤ succ b) : a ≤ b := by -- @exo
  obtain ⟨d, hd⟩ := h
  rw [succ_add] at hd
  exact ⟨d, succ_inj hd⟩

end Parcours.ℕ

#verifier
