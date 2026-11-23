/- @parcours
titre: Huit triangles et un point
difficulte: 2
requiert: Classiques.Triangulaires
indice: Utilise `gauss n` puis `grind`.
-/
import Solutions.Recurrence.Definitions
import Solutions.Recurrence.Gauss

/-!
# Huit triangles et un point

## Se le représenter
Prends 8 copies d'un triangle de côté `n` et un point : en les assemblant autour du point central,
on obtient un carré de côté `2n + 1`. (Diophante l'avait remarqué ; c'est un test pour savoir si un
nombre est triangulaire.)

## À prouver
`huit_triangles (n : Nat) : 8 * somme (fun i => i) (n + 1) + 1 = (2 * n + 1) ^ 2`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem huit_triangles (n : Nat) : 8 * somme (fun i => i) (n + 1) + 1 = (2 * n + 1) ^ 2 := by -- @exo
  have g := gauss n
  grind

end Parcours.Classiques

#verifier
