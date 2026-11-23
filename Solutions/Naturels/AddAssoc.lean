/- @parcours
titre: Associativité de l'addition
difficulte: 2
indice: Récurrence sur `c` (le dernier).
indice: Cas `succ` : `rw [add_succ, add_succ, add_succ, ih]`.
-/
import Solutions.Naturels.Base

/-!
# Associativité de l'addition

`(a + b) + c = a + (b + c)`. En Lean, `a + b + c` se lit `(a + b) + c`.

## À prouver
`add_assoc (a b c : ℕ) : a + b + c = a + (b + c)`

## Rappel
- `add_zero a : a + 0 = a`
- `add_succ a b : a + succ b = succ (a + b)`
-/

namespace Parcours.ℕ

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by -- @exo
  induction c with
  | zero => rfl
  | succ c ih => rw [add_succ, add_succ, add_succ, ih]

end Parcours.ℕ

#verifier
