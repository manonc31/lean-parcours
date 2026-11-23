/- @parcours
titre: La somme des Fibonacci
difficulte: 2
requiert: Recurrence.Fibonacci
indice: Récurrence ; `somme_succ` et `fib_add_two`, puis `omega`.
-/
import Solutions.Recurrence.Definitions

/-!
# La somme des Fibonacci

## Se le représenter
`0 + 1 + 1 + 2 + 3 + 5 + 8 = 20 = 21 − 1`. La somme des premiers Fibonacci est un Fibonacci moins 1 :
chaque nouveau terme « absorbe » les précédents.

## À prouver
`fib_somme (n : Nat) : somme fib n + 1 = fib (n + 1)`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fib_somme (n : Nat) : somme fib n + 1 = fib (n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, show n + 1 + 1 = n + 2 from rfl, fib_add_two]
    omega

end Parcours.Classiques

#verifier
