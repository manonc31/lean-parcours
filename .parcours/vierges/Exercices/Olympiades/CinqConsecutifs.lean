import Exercices.Arithmetique.Congruences

/-!
# Cinq entiers consécutifs

Le produit de 5 entiers consécutifs est toujours divisible par `5! = 120`. (En général, le produit
de `k` entiers consécutifs est divisible par `k!`, car le quotient est un coefficient binomial.)

Ici, on utilise **tes** lemmes de congruences : chaque facteur est congru à son reste modulo 120,
donc le produit aussi ; et il ne reste que 120 cas à vérifier.

## À prouver
`cinq_consecutifs : (n * (n + 1) * (n + 2) * (n + 3) * (n + 4)) % 120 = 0`

---
*Exercice* `Olympiades.CinqConsecutifs` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Olympiades.CinqConsecutifs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

open Parcours.Arith

theorem cinq_consecutifs (n : Nat) : (n * (n + 1) * (n + 2) * (n + 3) * (n + 4)) % 120 = 0 := by
  sorry

end Parcours.Olymp

#verifier
