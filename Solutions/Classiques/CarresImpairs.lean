/- @parcours
titre: La somme des carrés impairs
difficulte: 2
requiert: Recurrence.Carres
indice: Récurrence ; `somme_succ`, `Nat.mul_add`, puis `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# La somme des carrés impairs

## Se le représenter
`1² + 3² + 5² + ⋯ + (2n−1)² = n(2n−1)(2n+1)/3`. Sans division ni soustraction :
`3 × somme + n = 4n³`.

## À prouver
`carres_impairs (n : Nat) : 3 * somme (fun i => (2 * i + 1) ^ 2) n + n = 4 * n ^ 3`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem carres_impairs (n : Nat) : 3 * somme (fun i => (2 * i + 1) ^ 2) n + n = 4 * n ^ 3 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.mul_add]
    grind

end Parcours.Classiques

#verifier
