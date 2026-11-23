/- @parcours
titre: Deux triangles font un carré
difficulte: 2
requiert: Recurrence.Gauss
indice: `tri (n + 1) = tri n + (n + 1)` (`somme_succ`).
indice: Avec la somme de Gauss (`gauss n : 2 * tri n = n * (n + 1)`), c'est un calcul : `grind`.
-/
import Solutions.Recurrence.Definitions
import Solutions.Recurrence.Gauss

/-!
# Deux triangles font un carré

## Se le représenter
Le nombre triangulaire `T(n) = 0 + 1 + ⋯ + n` compte les points d'un triangle (les quilles au bowling :
`T(4) = 10`). Colle un triangle de côté `n` et un triangle de côté `n + 1` le long de la diagonale :
ils forment un **carré** `(n + 1) × (n + 1)`.

## À prouver
`deux_triangles (n : Nat) : tri n + tri (n + 1) = (n + 1) ^ 2` où `tri n = somme (fun i => i) (n + 1)`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

def tri (n : Nat) : Nat := somme (fun i => i) (n + 1)

theorem deux_triangles (n : Nat) : tri n + tri (n + 1) = (n + 1) ^ 2 := by -- @exo
  have g := gauss n
  unfold tri
  rw [somme_succ (fun i => i) (n + 1)]
  grind

end Parcours.Classiques

#verifier
