import Exercices.Recurrence.Definitions

/-!
# La factorielle bat le carré

## Se le représenter
`4! = 24 ≥ 16 = 4²`, `5! = 120 ≥ 25`… et ensuite chaque étape multiplie la factorielle par `n + 1`,
alors que le carré grandit beaucoup moins.

## À prouver
`fact_carre (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ fact n`

---
*Exercice* `Classiques.FactCarre` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Classiques.FactCarre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fact_carre (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ fact n := by
  sorry

end Parcours.Classiques

#verifier
