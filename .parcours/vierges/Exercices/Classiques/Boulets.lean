import Exercices.Classiques.Triangulaires
import Exercices.Classiques.CarresGrille

/-!
# La pile de boulets de canon

## Se le représenter
Une pile de boulets de canon à base **triangulaire** : chaque étage est un nombre triangulaire
(1, 3, 6, 10…). Le nombre total de boulets est un **nombre tétraédrique** : `1, 4, 10, 20, 35…`,
égal à `n(n+1)(n+2)/6`.

Pour une pile à base **carrée**, on additionne des carrés. Édouard Lucas (1875) a demandé : quand
une pile carrée contient-elle un nombre **carré** de boulets ? Seulement pour 1 étage… et pour
24 étages : `1² + 2² + ⋯ + 24² = 4900 = 70²` !

## À prouver
1. `tetraedrique : 6 * somme tri (n + 1) = n * (n + 1) * (n + 2)`
2. `lucas : carres 24 = 70 ^ 2`

## Ressources
- [Problème des boulets de canon (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Cannonball_problem)

---
*Exercice* `Classiques.Boulets` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.Boulets` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem tetraedrique (n : Nat) : 6 * somme tri (n + 1) = n * (n + 1) * (n + 2) := by
  sorry

theorem lucas : carres 24 = 70 ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
