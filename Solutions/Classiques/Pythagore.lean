/- @parcours
titre: Fabriquer des triangles rectangles
difficulte: 2
requiert: Olympiades.QuatreConsecutifs
indice: `grind` développe et compare.
indice: Essaie `m = 2, n = 1` : tu retrouves `(3, 4, 5)`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Fabriquer des triangles rectangles

## Se le représenter
`3² + 4² = 5²`, `5² + 12² = 13²`, `8² + 15² = 17²`… Euclide a trouvé une machine à fabriquer des
triplets de Pythagore : pour tous `m > n`, `(m² − n², 2mn, m² + n²)` en est un.

## À prouver
`euclide_pythagore (m n : Int) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2`, et `trois_quatre_cinq`

## Ressources
- [Triplet pythagoricien (Wikipédia)](https://fr.wikipedia.org/wiki/Triplet_pythagoricien)
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem euclide_pythagore (m n : Int) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by -- @exo
  grind

theorem trois_quatre_cinq : (3 : Nat) ^ 2 + 4 ^ 2 = 5 ^ 2 := by -- @exo
  decide

end Parcours.Classiques

#verifier
