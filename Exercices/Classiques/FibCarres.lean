import Exercices.Recurrence.Definitions

/-!
# Le rectangle d'or des Fibonacci

## Se le représenter
Dessine des carrés de côtés `1, 1, 2, 3, 5, 8, …` en spirale : ils remplissent exactement un rectangle
de côtés `F(n)` et `F(n+1)`. Donc la somme des carrés des Fibonacci est `F(n)·F(n+1)`.
(C'est la figure de la « spirale d'or ».)

## À prouver
`fib_carres (n : Nat) : somme (fun i => fib i ^ 2) (n + 1) = fib n * fib (n + 1)`

---
*Exercice* `Classiques.FibCarres` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Classiques.FibCarres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fib_carres (n : Nat) : somme (fun i => fib i ^ 2) (n + 1) = fib n * fib (n + 1) := by
  sorry

end Parcours.Classiques

#verifier
