/- @parcours
titre: Premières puissances
difficulte: 2
indice: `zero_pow_succ` : `rw [pow_succ, mul_zero]`.
indice: `pow_one` : `rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]`.
indice: `one_pow` : récurrence, cas `succ` : `rw [pow_succ, ih, mul_one]`.
-/
import Solutions.Naturels.Puissance
import Solutions.Naturels.MulBase

/-!
# Premières puissances

## À prouver
1. `zero_pow_succ (n : ℕ) : (0 : ℕ) ^ succ n = 0`
2. `pow_one (a : ℕ) : a ^ (1 : ℕ) = a`
3. `one_pow (n : ℕ) : (1 : ℕ) ^ n = 1`
-/

namespace Parcours.ℕ

theorem zero_pow_succ (n : ℕ) : (0 : ℕ) ^ succ n = 0 := by -- @exo
  rw [pow_succ, mul_zero]

theorem pow_one (a : ℕ) : a ^ (1 : ℕ) = a := by -- @exo
  rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]

theorem one_pow (n : ℕ) : (1 : ℕ) ^ n = 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, mul_one]

end Parcours.ℕ

#verifier
