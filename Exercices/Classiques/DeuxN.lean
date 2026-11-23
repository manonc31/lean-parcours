import Exercices.Recurrence.Definitions

/-!
# Doubler bat ajouter

## Se le représenter
Doubler à chaque étape (`2ⁿ`) va toujours au moins aussi vite qu'ajouter 2 à chaque étape (`2n`).

## À prouver
`deux_n (n : Nat) : 2 * n ≤ 2 ^ n`

---
*Exercice* `Classiques.DeuxN` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.DeuxN` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem deux_n (n : Nat) : 2 * n ≤ 2 ^ n := by
  sorry

end Parcours.Classiques

#verifier
