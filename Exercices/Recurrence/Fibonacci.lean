import Exercices.Recurrence.Definitions

/-!
# Les nombres de Fibonacci

`0, 1, 1, 2, 3, 5, 8, 13, 21, 34…` : chaque terme est la somme des deux précédents.
Pour les propriétés qui regardent deux termes en arrière, une astuce : prouver **deux
énoncés à la fois** (`P n ∧ P (n+1)`) par récurrence.

## À prouver
1. `fib_lt_deux_pow (n : Nat) : fib n < 2 ^ n`
2. `fib_add (m n : Nat) : fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n`

## Ressources
- [Suite de Fibonacci (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Fibonacci)

---
*Exercice* `Recurrence.Fibonacci` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.Fibonacci` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem fib_lt_deux_pow (n : Nat) : fib n < 2 ^ n := by
  sorry

theorem fib_add (m n : Nat) : fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n := by
  sorry

end Parcours.Recurrence

#verifier
