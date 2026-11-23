/- @parcours
titre: Les puissances de 3
difficulte: 2
requiert: Recurrence.Geometrique
indice: Récurrence ; `somme_succ`, `Nat.pow_succ`, puis `omega`.
-/
import Solutions.Recurrence.Definitions

/-!
# Les puissances de 3

## Se le représenter
`1 + 3 + 9 + 27 = 40` et `2 × 40 + 1 = 81 = 3⁴`. Tout comme `1 + 2 + 4 + ⋯ = 2ⁿ − 1` en binaire,
en base 3 : `222…2` (n chiffres) plus 1 donne `1000…0`.

## À prouver
`puissances_trois (n : Nat) : 2 * somme (fun i => 3 ^ i) n + 1 = 3 ^ n`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem puissances_trois (n : Nat) : 2 * somme (fun i => 3 ^ i) n + 1 = 3 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.pow_succ]
    omega

end Parcours.Classiques

#verifier
