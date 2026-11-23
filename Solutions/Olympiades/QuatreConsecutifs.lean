/- @parcours
titre: Quatre entiers consécutifs
difficulte: 2
requiert: Olympiades.Parite
indice: Développe les deux côtés… ou laisse `grind` le faire.
indice: Pour deviner le carré : `1·2·3·4 + 1 = 25 = 5²`, `2·3·4·5 + 1 = 121 = 11²`… et `5 = 1² + 3·1 + 1`, `11 = 2² + 3·2 + 1`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Quatre entiers consécutifs

> Le produit de quatre entiers consécutifs, plus 1, est toujours un carré parfait.

`1·2·3·4 + 1 = 25`, `2·3·4·5 + 1 = 121`, `3·4·5·6 + 1 = 361`… Lequel ? `(n² + 3n + 1)²`.

## À prouver
`quatre_consecutifs : n * (n + 1) * (n + 2) * (n + 3) + 1 = (n * n + 3 * n + 1) ^ 2`
-/

namespace Parcours.Olymp

theorem quatre_consecutifs (n : Nat) :
    n * (n + 1) * (n + 2) * (n + 3) + 1 = (n * n + 3 * n + 1) ^ 2 := by -- @exo
  grind

end Parcours.Olymp

#verifier
