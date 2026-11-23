/- @parcours
titre: L'identité de Sophie Germain
difficulte: 2
requiert: Classiques.Pythagore
indice: `grind`. Mais essaie de voir la différence de carrés avant !
-/
import Solutions.Arithmetique.Definitions

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
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem sophie_germain (n : Int) : n ^ 4 + 4 = (n ^ 2 + 2 * n + 2) * (n ^ 2 - 2 * n + 2) := by -- @exo
  grind

end Parcours.Classiques

#verifier
