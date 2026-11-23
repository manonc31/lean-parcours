import Exercices.Arithmetique.Definitions

/-!
# n³ + 2n est divisible par 3

## Se le représenter
`n³ + 2n = n³ − n + 3n = (n−1)n(n+1) + 3n` : trois entiers consécutifs contiennent toujours un multiple
de 3. En Lean, on raisonne directement sur le reste de `n` modulo 3.

## À prouver
`divisible_trois (n : Nat) : (n * n * n + 2 * n) % 3 = 0`

---
*Exercice* `Classiques.Divisible3` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.Divisible3` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem divisible_trois (n : Nat) : (n * n * n + 2 * n) % 3 = 0 := by
  sorry

end Parcours.Classiques

#verifier
