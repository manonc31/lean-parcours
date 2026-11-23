import Exercices.Recurrence.Definitions

/-!
# Combien de carrés sur un échiquier ?

## Se le représenter
Sur un échiquier `n × n`, combien de carrés de toutes tailles ? Pour la taille `k`, il y en a
`(n − k + 1)²`. Au total : `1² + 2² + ⋯ + n²`. Pour un échiquier 8 × 8 : 204 carrés ! On définit
`carres (n + 1) = carres n + (n + 1)²` (agrandir la grille d'un rang ajoute `(n+1)²` carrés).

## À prouver
`carres_grille (n : Nat) : 6 * carres n = n * (n + 1) * (2 * n + 1)`, et `carres 8 = 204`

---
*Exercice* `Classiques.CarresGrille` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Classiques.CarresGrille` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

def carres : Nat → Nat
  | 0 => 0
  | n + 1 => carres n + (n + 1) ^ 2

theorem carres_grille (n : Nat) : 6 * carres n = n * (n + 1) * (2 * n + 1) := by
  sorry

theorem echiquier : carres 8 = 204 := by
  sorry

end Parcours.Classiques

#verifier
