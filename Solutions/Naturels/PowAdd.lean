/- @parcours
titre: Puissance d'une somme d'exposants
difficulte: 3
indice: Récurrence sur `n`. Cas `zero` : `rw [add_zero, pow_zero, mul_one]`.
indice: Cas `succ` : `rw [add_succ, pow_succ, pow_succ, ih, mul_assoc]`.
-/
import Solutions.Naturels.PowBase
import Solutions.Naturels.MulAssoc

/-!
# Puissance d'une somme d'exposants

`a^(m+n) = a^m × a^n`.

## À prouver
`pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n`
-/

namespace Parcours.ℕ

theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by -- @exo
  induction n with
  | zero => rw [add_zero, pow_zero, mul_one]
  | succ n ih => rw [add_succ, pow_succ, pow_succ, ih, mul_assoc]

end Parcours.ℕ

#verifier
