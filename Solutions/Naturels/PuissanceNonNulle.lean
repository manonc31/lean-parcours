/- @parcours
titre: Une puissance non nulle
difficulte: 2
requiert: Naturels.PowBase
indice: Récurrence sur `n`. Cas `zero` : `a ^ 0 = 1 = succ 0 ≠ 0`.
indice: Cas `succ` : `aⁿ⁺¹ = aⁿ × a = 0` donnerait `aⁿ = 0` ou `a = 0` (`mul_eq_zero`).
-/
import Solutions.Naturels.PowBase
import Solutions.Naturels.MulEqZero

/-!
# Une puissance non nulle

Si `a ≠ 0`, alors `aⁿ ≠ 0`.

## À prouver
`pow_ne_zero (a n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0`
-/

namespace Parcours.ℕ

theorem pow_ne_zero (a n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by -- @exo
  induction n with
  | zero =>
    rw [pow_zero, one_eq_succ_zero]
    exact succ_ne_zero 0
  | succ n ih =>
    intro h
    rw [pow_succ] at h
    rcases mul_eq_zero _ _ h with h1 | h1
    · exact ih h1
    · exact ha h1

end Parcours.ℕ

#verifier
