/- @parcours
titre: La formule d'addition de Fibonacci
difficulte: 3
requiert: Recurrence.Cassini
indice: Récurrence « à la Fibonacci » : `induction n using fib.induct` donne les cas 0, 1 et `n + 2` avec deux hypothèses de récurrence.
indice: Dans le dernier cas, développe `fib (m + n + 3)` et `fib (n + 3)` avec `fib_add_two`, puis `grind`.
indice: `fib_double` : prends `m = n`.
-/
import Solutions.Recurrence.Definitions

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
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fib_addition (m n : Nat) :
    fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n := by -- @exo
  induction n using fib.induct with
  | case1 => simp [fib]
  | case2 =>
    simp [fib]
    omega
  | case3 n ih1 ih2 =>
    have h1 : fib (m + (n + 2) + 1) = fib (m + n + 1) + fib (m + (n + 1) + 1) := by
      rw [show m + (n + 2) + 1 = (m + n + 1) + 2 by omega, fib_add_two]
      rfl
    have h2 : fib (n + 1 + 1 + 1) = fib (n + 1) + fib (n + 1 + 1) := fib_add_two (n + 1)
    have h3 : fib (n + 1 + 1) = fib n + fib (n + 1) := fib_add_two n
    show fib (m + (n + 2) + 1) = fib (m + 1) * fib (n + 1 + 1 + 1) + fib m * fib (n + 1 + 1)
    rw [h1, ih1, ih2, h2, h3]
    grind

theorem fib_double (n : Nat) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := by -- @exo
  rw [show 2 * n + 1 = n + n + 1 by omega, fib_addition]
  grind

end Parcours.Classiques

#verifier
