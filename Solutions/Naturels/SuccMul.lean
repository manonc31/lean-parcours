/- @parcours
titre: Successeur à gauche, version ×
difficulte: 3
indice: Récurrence sur `b`. Le cas `zero` est vrai par définition.
indice: Cas `succ` : après `rw [mul_succ, mul_succ, ih]`, il faut montrer `a * b + b + succ a = a * b + a + succ b`.
indice: `rw [add_succ, add_succ, add_right_comm]`.
-/
import Solutions.Naturels.Multiplication
import Solutions.Naturels.AddRightComm

/-!
# Successeur à gauche, version multiplicative

`(a + 1) × b = a × b + b`. C'est la clé de la commutativité de la multiplication.

## À prouver
`succ_mul (a b : ℕ) : succ a * b = a * b + b`
-/

namespace Parcours.ℕ

theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by -- @exo
  induction b with
  | zero => rfl
  | succ b ih => rw [mul_succ, mul_succ, ih, add_succ, add_succ, add_right_comm]

end Parcours.ℕ

#verifier
