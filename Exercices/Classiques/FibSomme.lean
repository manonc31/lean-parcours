import Exercices.Recurrence.Definitions

/-!
# La somme des Fibonacci

## Se le représenter
`0 + 1 + 1 + 2 + 3 + 5 + 8 = 20 = 21 − 1`. La somme des premiers Fibonacci est un Fibonacci moins 1 :
chaque nouveau terme « absorbe » les précédents.

## À prouver
`fib_somme (n : Nat) : somme fib n + 1 = fib (n + 1)`

---
*Exercice* `Classiques.FibSomme` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.FibSomme` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fib_somme (n : Nat) : somme fib n + 1 = fib (n + 1) := by
  sorry

end Parcours.Classiques

#verifier
