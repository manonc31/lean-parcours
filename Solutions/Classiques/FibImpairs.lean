/- @parcours
titre: Les Fibonacci d'indice impair
difficulte: 3
requiert: Classiques.FibSomme
indice: Récurrence ; `2 * (n + 1) = 2 * n + 2`, puis `fib_add_two`.
-/
import Solutions.Recurrence.Definitions

/-!
# Les Fibonacci d'indice impair

## Se le représenter
`F(1) + F(3) + F(5) = 1 + 2 + 5 = 8 = F(6)`. Chaque terme d'indice pair est la somme du terme
précédent (pair) et d'un terme impair : en déroulant, les impairs s'additionnent.

## À prouver
`fib_impairs (n : Nat) : somme (fun i => fib (2 * i + 1)) n = fib (2 * n)`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fib_impairs (n : Nat) : somme (fun i => fib (2 * i + 1)) n = fib (2 * n) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, ih, show 2 * (n + 1) = 2 * n + 2 by omega, fib_add_two]

end Parcours.Classiques

#verifier
