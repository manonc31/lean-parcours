import Exercices.Recurrence.Definitions

/-!
# Les Fibonacci d'indice impair

## Se le représenter
`F(1) + F(3) + F(5) = 1 + 2 + 5 = 8 = F(6)`. Chaque terme d'indice pair est la somme du terme
précédent (pair) et d'un terme impair : en déroulant, les impairs s'additionnent.

## À prouver
`fib_impairs (n : Nat) : somme (fun i => fib (2 * i + 1)) n = fib (2 * n)`

---
*Exercice* `Classiques.FibImpairs` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Classiques.FibImpairs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fib_impairs (n : Nat) : somme (fun i => fib (2 * i + 1)) n = fib (2 * n) := by
  sorry

end Parcours.Classiques

#verifier
