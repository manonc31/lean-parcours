import Exercices.Arithmetique.PgcdDivise
import Exercices.Recurrence.Fibonacci

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

---
*Exercice* `Arithmetique.FibonacciPgcd` · difficulté ★★★★★

💡 Indices : `./parcours indice Arithmetique.FibonacciPgcd` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

open Parcours.Recurrence

theorem pgcd_fib (m n : Nat) : pgcd (fib m) (fib n) = fib (pgcd m n) := by
  sorry

end Parcours.Arith

#verifier
