/- @parcours
titre: Un produit nul
difficulte: 3
indice: Raisonne par cas sur `b` (`cases b with`).
indice: Si `b = succ b'`, `mul_succ` transforme `h` en `a * b' + a = 0`, et `add_eq_zero` conclut.
-/
import Solutions.Naturels.Multiplication
import Solutions.Naturels.SommeNulle

/-!
# Un produit nul

Si `a × b = 0`, alors `a = 0` ou `b = 0`. (On dit que ℕ est « intègre ».)

## À prouver
`mul_eq_zero (a b : ℕ) : a * b = 0 → a = 0 ∨ b = 0`
-/

namespace Parcours.ℕ

theorem mul_eq_zero (a b : ℕ) : a * b = 0 → a = 0 ∨ b = 0 := by -- @exo
  intro h
  cases b with
  | zero => exact Or.inr rfl
  | succ b =>
    rw [mul_succ] at h
    exact Or.inl (add_eq_zero _ _ h).2

end Parcours.ℕ

#verifier
