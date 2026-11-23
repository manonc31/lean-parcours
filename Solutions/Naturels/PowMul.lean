/- @parcours
titre: Puissances de produits
difficulte: 3
indice: `mul_pow` : récurrence sur `n`. Cas `succ`, après `rw [pow_succ, pow_succ, pow_succ, ih]`, il faut réarranger `a^n * b^n * (a * b)` en `a^n * a * (b^n * b)` : `mul_assoc`, `mul_left_comm`…
indice: Par exemple : `rw [mul_assoc, mul_left_comm (b ^ n) a b, ← mul_assoc]`.
indice: `pow_mul` : récurrence sur `n` ; cas `succ` : `rw [mul_succ, pow_add, ih, pow_succ]`.
-/
import Solutions.Naturels.PowAdd
import Solutions.Naturels.AddMul

/-!
# Puissances de produits

## À prouver
1. `mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n`
2. `pow_mul (a m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n`
-/

namespace Parcours.ℕ

theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, pow_succ, ih, mul_assoc, mul_left_comm (b ^ n) a b, ← mul_assoc]

theorem pow_mul (a m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [mul_succ, pow_add, ih, pow_succ]

end Parcours.ℕ

#verifier
