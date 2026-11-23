import Exercices.Recurrence.Definitions

/-!
# Les puissances de 3

## Se le représenter
`1 + 3 + 9 + 27 = 40` et `2 × 40 + 1 = 81 = 3⁴`. Tout comme `1 + 2 + 4 + ⋯ = 2ⁿ − 1` en binaire,
en base 3 : `222…2` (n chiffres) plus 1 donne `1000…0`.

## À prouver
`puissances_trois (n : Nat) : 2 * somme (fun i => 3 ^ i) n + 1 = 3 ^ n`

---
*Exercice* `Classiques.PuissancesTrois` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.PuissancesTrois` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem puissances_trois (n : Nat) : 2 * somme (fun i => 3 ^ i) n + 1 = 3 ^ n := by
  sorry

end Parcours.Classiques

#verifier
