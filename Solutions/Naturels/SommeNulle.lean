/- @parcours
titre: Une somme nulle
difficulte: 2
indice: `succ_ne_zero` : `intro h`, puis utilise `zero_ne_succ` (attention au sens de l'égalité : `h.symm` ou `Eq.symm h`).
indice: `add_eq_zero` : raisonne par cas sur `b` avec `cases b with`.
indice: Si `b = succ b'`, alors `a + succ b' = succ (a + b')` ne peut pas valoir `0`.
-/
import Solutions.Naturels.Base

/-!
# Une somme nulle

Dans ℕ, une somme est nulle seulement si les deux termes le sont. (Faux dans ℤ : `1 + (-1) = 0` !)

La tactique **`cases n with`** raisonne par cas : `n = 0` ou `n = succ m`, sans hypothèse de récurrence.

## À prouver
1. `succ_ne_zero (a : ℕ) : succ a ≠ 0`
2. `add_eq_zero (a b : ℕ) : a + b = 0 → a = 0 ∧ b = 0`
-/

namespace Parcours.ℕ

theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by -- @exo
  intro h
  exact zero_ne_succ a h.symm

theorem add_eq_zero (a b : ℕ) : a + b = 0 → a = 0 ∧ b = 0 := by -- @exo
  intro h
  cases b with
  | zero => exact ⟨h, rfl⟩
  | succ b =>
    rw [add_succ] at h
    exact absurd h (succ_ne_zero _)

end Parcours.ℕ

#verifier
