/- @parcours
titre: Trois puissance n
difficulte: 2
requiert: Recurrence.Croissance
indice: Récurrence ; `Nat.pow_succ` sur les deux puissances.
indice: Il faut savoir que `2 ^ n ≥ 1` (`Nat.one_le_two_pow`), puis `omega`.
-/
import Solutions.Recurrence.Definitions

/-!
# Trois puissance n

`3ⁿ ≥ 2ⁿ + n` pour tout `n`.

## À prouver
`trois_puissance (n : Nat) : 2 ^ n + n ≤ 3 ^ n`
-/

namespace Parcours.Recurrence

theorem trois_puissance (n : Nat) : 2 ^ n + n ≤ 3 ^ n := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.pow_succ, Nat.pow_succ]
    omega

end Parcours.Recurrence

#verifier
