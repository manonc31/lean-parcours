/- @parcours
titre: La somme des cubes impairs
difficulte: 2
requiert: Classiques.CarresImpairs
indice: Récurrence ; `somme_succ`, puis `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# La somme des cubes impairs

## Se le représenter
`1³ = 1`, `1³ + 3³ = 28`, `1³ + 3³ + 5³ = 153`… La formule : `n²(2n² − 1)`. Sans soustraction :
`somme + n² = 2n⁴`.

## À prouver
`cubes_impairs : somme (fun i => (2 * i + 1) ^ 3) n + n ^ 2 = 2 * n ^ 4`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem cubes_impairs (n : Nat) : somme (fun i => (2 * i + 1) ^ 3) n + n ^ 2 = 2 * n ^ 4 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ]
    grind

end Parcours.Classiques

#verifier
