/- @parcours
titre: Les nombres pentagonaux
difficulte: 2
requiert: Classiques.Triangulaires
indice: Récurrence ; déplie `pent` (`simp only [pent]`), puis `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# Les nombres pentagonaux

## Se le représenter
`1, 5, 12, 22, 35, …` : les points de pentagones emboîtés. On passe d'un pentagone au suivant en
ajoutant trois côtés de `n + 1` points, moins les deux coins partagés : `3n + 1` points.
Formule : `P(n) = n(3n − 1)/2`.

## À prouver
`pentagonaux (n : Nat) : 2 * pent n + n = 3 * n ^ 2`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

def pent : Nat → Nat
  | 0 => 0
  | n + 1 => pent n + 3 * n + 1

theorem pentagonaux (n : Nat) : 2 * pent n + n = 3 * n ^ 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pent]
    grind

end Parcours.Classiques

#verifier
