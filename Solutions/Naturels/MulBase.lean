/- @parcours
titre: Multiplier par 0 et par 1
difficulte: 2
indice: `zero_mul` : récurrence sur `a`. Cas `succ` : `rw [mul_succ, ih]` puis il reste `0 + 0 = 0`.
indice: `mul_one` : `rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]`.
indice: `one_mul` : récurrence. Cas `succ` : `rw [mul_succ, ih, succ_eq_add_one]`.
-/
import Solutions.Naturels.Multiplication
import Solutions.Naturels.Successeur

/-!
# Multiplier par 0 et par 1

## À prouver
1. `zero_mul (a : ℕ) : 0 * a = 0`
2. `mul_one (a : ℕ) : a * 1 = a`
3. `one_mul (a : ℕ) : 1 * a = a`

## Rappel
`mul_zero a : a * 0 = 0`, `mul_succ a b : a * succ b = a * b + a`, `one_eq_succ_zero`, `succ_eq_add_one`.
-/

namespace Parcours.ℕ

theorem zero_mul (a : ℕ) : 0 * a = 0 := by -- @exo
  induction a with
  | zero => rfl
  | succ a ih => rw [mul_succ, ih]; rfl

theorem mul_one (a : ℕ) : a * 1 = a := by -- @exo
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

theorem one_mul (a : ℕ) : 1 * a = a := by -- @exo
  induction a with
  | zero => rfl
  | succ a ih => rw [mul_succ, ih, succ_eq_add_one]

end Parcours.ℕ

#verifier
