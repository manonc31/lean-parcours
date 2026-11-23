/- @parcours
titre: Commutativité de la multiplication
difficulte: 3
indice: Récurrence sur `b`.
indice: Cas `zero` : `rw [mul_zero, zero_mul]`. Cas `succ` : `rw [mul_succ, succ_mul, ih]`.
-/
import Solutions.Naturels.SuccMul
import Solutions.Naturels.MulBase

/-!
# Commutativité de la multiplication

## À prouver
`mul_comm (a b : ℕ) : a * b = b * a`
-/

namespace Parcours.ℕ

theorem mul_comm (a b : ℕ) : a * b = b * a := by -- @exo
  induction b with
  | zero => rw [mul_zero, zero_mul]
  | succ b ih => rw [mul_succ, succ_mul, ih]

end Parcours.ℕ

#verifier
