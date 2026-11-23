import Exercices.Recurrence.Definitions

/-!
# La somme des cubes impairs

## Se le représenter
`1³ = 1`, `1³ + 3³ = 28`, `1³ + 3³ + 5³ = 153`… La formule : `n²(2n² − 1)`. Sans soustraction :
`somme + n² = 2n⁴`.

## À prouver
`cubes_impairs : somme (fun i => (2 * i + 1) ^ 3) n + n ^ 2 = 2 * n ^ 4`

---
*Exercice* `Classiques.CubesImpairs` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.CubesImpairs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem cubes_impairs (n : Nat) : somme (fun i => (2 * i + 1) ^ 3) n + n ^ 2 = 2 * n ^ 4 := by
  sorry

end Parcours.Classiques

#verifier
