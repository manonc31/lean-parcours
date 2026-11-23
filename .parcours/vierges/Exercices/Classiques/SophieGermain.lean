import Exercices.Arithmetique.Definitions

/-!
# L'identité de Sophie Germain

## Se le représenter
`n⁴ + 4 = (n² + 2n + 2)(n² − 2n + 2)`. Astuce : `n⁴ + 4 = (n² + 2)² − (2n)²`, une différence de
carrés ! Conséquence : `n⁴ + 4` n'est jamais premier pour `n > 1`. (Sophie Germain, mathématicienne
française autodidacte, 1776–1831.)

## À prouver
`sophie_germain (n : Int) : n ^ 4 + 4 = (n ^ 2 + 2 * n + 2) * (n ^ 2 - 2 * n + 2)`

## Ressources
- [Sophie Germain (Wikipédia)](https://fr.wikipedia.org/wiki/Sophie_Germain)

---
*Exercice* `Classiques.SophieGermain` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.SophieGermain` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem sophie_germain (n : Int) : n ^ 4 + 4 = (n ^ 2 + 2 * n + 2) * (n ^ 2 - 2 * n + 2) := by
  sorry

end Parcours.Classiques

#verifier
