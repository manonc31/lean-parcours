/- @parcours
titre: Associativité de la multiplication
difficulte: 3
indice: Récurrence sur `c`.
indice: Cas `succ` : `rw [mul_succ, mul_succ, mul_add, ih]`.
-/
import Solutions.Naturels.MulAdd

/-!
# Associativité de la multiplication

## À prouver
`mul_assoc (a b c : ℕ) : a * b * c = a * (b * c)`
-/

namespace Parcours.ℕ

theorem mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := by -- @exo
  induction c with
  | zero => rfl
  | succ c ih => rw [mul_succ, mul_succ, mul_add, ih]

end Parcours.ℕ

#verifier
