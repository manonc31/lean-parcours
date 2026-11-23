import Exercices.Recurrence.Definitions

/-!
# La somme des carrés impairs

## Se le représenter
`1² + 3² + 5² + ⋯ + (2n−1)² = n(2n−1)(2n+1)/3`. Sans division ni soustraction :
`3 × somme + n = 4n³`.

## À prouver
`carres_impairs (n : Nat) : 3 * somme (fun i => (2 * i + 1) ^ 2) n + n = 4 * n ^ 3`

---
*Exercice* `Classiques.CarresImpairs` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.CarresImpairs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem carres_impairs (n : Nat) : 3 * somme (fun i => (2 * i + 1) ^ 2) n + n = 4 * n ^ 3 := by
  sorry

end Parcours.Classiques

#verifier
