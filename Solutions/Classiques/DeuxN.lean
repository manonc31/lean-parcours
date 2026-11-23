/- @parcours
titre: Doubler bat ajouter
difficulte: 1
requiert: Recurrence.Croissance
indice: Récurrence ; `Nat.pow_succ`, et `2 ^ n ≥ 1` (`Nat.one_le_two_pow`), puis `omega`.
-/
import Solutions.Recurrence.Definitions

/-!
# Doubler bat ajouter

## Se le représenter
Doubler à chaque étape (`2ⁿ`) va toujours au moins aussi vite qu'ajouter 2 à chaque étape (`2n`).

## À prouver
`deux_n (n : Nat) : 2 * n ≤ 2 ^ n`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem deux_n (n : Nat) : 2 * n ≤ 2 ^ n := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.pow_succ]
    omega

end Parcours.Classiques

#verifier
