/- @parcours
titre: Le rectangle d'or des Fibonacci
difficulte: 3
requiert: Classiques.FibSomme
indice: Récurrence ; `somme_succ`, `ih`, puis `fib_add_two` et `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# Le rectangle d'or des Fibonacci

## Se le représenter
Dessine des carrés de côtés `1, 1, 2, 3, 5, 8, …` en spirale : ils remplissent exactement un rectangle
de côtés `F(n)` et `F(n+1)`. Donc la somme des carrés des Fibonacci est `F(n)·F(n+1)`.
(C'est la figure de la « spirale d'or ».)

## À prouver
`fib_carres (n : Nat) : somme (fun i => fib i ^ 2) (n + 1) = fib n * fib (n + 1)`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fib_carres (n : Nat) : somme (fun i => fib i ^ 2) (n + 1) = fib n * fib (n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, ih, show n + 1 + 1 = n + 2 from rfl, fib_add_two]
    grind

end Parcours.Classiques

#verifier
