import Exercices.Recurrence.Definitions

/-!
# La formule d'addition de Fibonacci

## Se le représenter
Pour monter un escalier de `m + n + 1` marches par pas de 1 ou 2 (il y a `F(k+1)` façons pour
`k` marches) : soit on pose le pied sur la marche `m`, soit on l'enjambe (on passe de `m − 1` à
`m + 1`). D'où `F(m + n + 1) = F(m + 1) F(n + 1) + F(m) F(n)`.

## À prouver
1. `fib_addition : fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n`
2. `fib_double : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2`

## Ressources
- [Nombres de Fibonacci (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Fibonacci)

---
*Exercice* `Classiques.FibAddition` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Classiques.FibAddition` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fib_addition (m n : Nat) :
    fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n := by
  sorry

theorem fib_double (n : Nat) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
