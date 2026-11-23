import Exercices.Recurrence.Definitions
import Exercices.Recurrence.Gauss

/-!
# Deux triangles font un carré

## Se le représenter
Le nombre triangulaire `T(n) = 0 + 1 + ⋯ + n` compte les points d'un triangle (les quilles au bowling :
`T(4) = 10`). Colle un triangle de côté `n` et un triangle de côté `n + 1` le long de la diagonale :
ils forment un **carré** `(n + 1) × (n + 1)`.

## À prouver
`deux_triangles (n : Nat) : tri n + tri (n + 1) = (n + 1) ^ 2` où `tri n = somme (fun i => i) (n + 1)`

---
*Exercice* `Classiques.Triangulaires` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.Triangulaires` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

def tri (n : Nat) : Nat := somme (fun i => i) (n + 1)

theorem deux_triangles (n : Nat) : tri n + tri (n + 1) = (n + 1) ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
