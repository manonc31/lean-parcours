import Exercices.Recurrence.Definitions

/-!
# La somme des nombres pairs

## Se le représenter
Empile les nombres pairs `0, 2, 4, …, 2(n−1)` en colonnes de points : tu obtiens un rectangle
`n × (n − 1)` (deux escaliers identiques collés). Donc la somme vaut `n(n − 1)`.

## À prouver
`somme_pairs (n : Nat) : somme (fun i => 2 * i) n + n = n * n` (c'est-à-dire `n(n − 1)`, sans soustraction)

---
*Exercice* `Classiques.SommePairs` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.SommePairs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem somme_pairs (n : Nat) : somme (fun i => 2 * i) n + n = n * n := by
  sorry

end Parcours.Classiques

#verifier
