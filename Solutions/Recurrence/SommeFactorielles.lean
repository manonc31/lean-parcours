/- @parcours
titre: Une somme de factorielles
difficulte: 3
requiert: Recurrence.Croissance
indice: Récurrence ; `somme_succ` et `fact_succ`.
indice: `(n+2)! = (n+2)(n+1)! = (n+1)(n+1)! + (n+1)!` : `grind` avec l'hypothèse de récurrence.
-/
import Solutions.Recurrence.Definitions

/-!
# Une somme de factorielles

`0·0! + 1·1! + 2·2! + ⋯ + n·n! = (n+1)! − 1`. (Joli : `1 + 4 + 18 = 23 = 4! − 1`.)

## À prouver
`somme_factorielles (n : Nat) : somme (fun k => k * fact k) (n + 1) + 1 = fact (n + 1)`
-/

namespace Parcours.Recurrence

theorem somme_factorielles (n : Nat) : somme (fun k => k * fact k) (n + 1) + 1 = fact (n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, fact_succ (n + 1)]
    grind

end Parcours.Recurrence

#verifier
