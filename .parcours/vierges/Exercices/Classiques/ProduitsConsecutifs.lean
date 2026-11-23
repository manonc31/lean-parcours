import Exercices.Recurrence.Definitions

/-!
# La somme des produits consécutifs

## Se le représenter
`1·2 + 2·3 + 3·4 + ⋯ + n(n+1) = n(n+1)(n+2)/3`. Visuellement : des « boîtes » `i × (i+1)` qui
s'empilent en une pyramide dont le volume est un tiers d'un pavé.

## À prouver
`produits_consecutifs (n : Nat) : 3 * somme (fun i => i * (i + 1)) (n + 1) = n * (n + 1) * (n + 2)`

---
*Exercice* `Classiques.ProduitsConsecutifs` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.ProduitsConsecutifs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem produits_consecutifs (n : Nat) :
    3 * somme (fun i => i * (i + 1)) (n + 1) = n * (n + 1) * (n + 2) := by
  sorry

end Parcours.Classiques

#verifier
