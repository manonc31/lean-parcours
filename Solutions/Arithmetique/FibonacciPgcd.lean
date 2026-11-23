/- @parcours
titre: Le PGCD des nombres de Fibonacci
difficulte: 5
genre: boss
solution: non
indice: Étape 1 : deux Fibonacci consécutifs sont premiers entre eux : `pgcd (fib n) (fib (n + 1)) = 1`.
indice: Étape 2 : avec `fib_add`, montre `pgcd (fib (m + n)) (fib n) = pgcd (fib m) (fib n)`.
indice: Étape 3 : donc `pgcd (fib m) (fib n)` « suit » l'algorithme d'Euclide sur `m, n` : `fun_induction pgcd m n`. Il faudra aussi relier `m % n` à des soustractions répétées.
-/
import Solutions.Arithmetique.PgcdDivise
import Solutions.Recurrence.Fibonacci

/-!
# 💀 Le PGCD des nombres de Fibonacci

Une propriété magique : `pgcd(F(m), F(n)) = F(pgcd(m, n))`.
Par exemple `pgcd(F(12), F(18)) = pgcd(144, 2584) = 8 = F(6)`.
Conséquence : `F(m)` divise `F(n)` dès que `m` divise `n`.

Boss sans solution de référence.

## À prouver
`pgcd_fib (m n : Nat) : pgcd (fib m) (fib n) = fib (pgcd m n)`

## Ressources
- [Suite de Fibonacci, propriétés de divisibilité (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Fibonacci)
-/

namespace Parcours.Arith

open Parcours.Recurrence

theorem pgcd_fib (m n : Nat) : pgcd (fib m) (fib n) = fib (pgcd m n) := by -- @exo
  sorry

end Parcours.Arith

#verifier
