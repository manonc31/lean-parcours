import Exercices.Recurrence.Definitions
import Exercices.Recurrence.Gauss

/-!
# Huit triangles et un point

## Se le représenter
Prends 8 copies d'un triangle de côté `n` et un point : en les assemblant autour du point central,
on obtient un carré de côté `2n + 1`. (Diophante l'avait remarqué ; c'est un test pour savoir si un
nombre est triangulaire.)

## À prouver
`huit_triangles (n : Nat) : 8 * somme (fun i => i) (n + 1) + 1 = (2 * n + 1) ^ 2`

---
*Exercice* `Classiques.HuitTriangles` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.HuitTriangles` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem huit_triangles (n : Nat) : 8 * somme (fun i => i) (n + 1) + 1 = (2 * n + 1) ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
