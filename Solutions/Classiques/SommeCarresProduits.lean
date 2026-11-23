/- @parcours
titre: x² + y² + z² ≥ xy + yz + zx
difficulte: 2
requiert: Classiques.CauchySchwarz
indice: Trois carrés positifs (`carre_positif`), puis `grind`.
-/
import Solutions.Classiques.CauchySchwarz

/-!
# x² + y² + z² ≥ xy + yz + zx

## Se le représenter
Additionne les trois carrés `(x − y)²`, `(y − z)²`, `(z − x)²` : c'est positif, et ça vaut
`2(x² + y² + z²) − 2(xy + yz + zx)`.

## À prouver
`somme_carres_produits : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2`
-/

namespace Parcours.Classiques

theorem somme_carres_produits (x y z : Int) : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2 := by -- @exo
  have h1 := carre_positif (x - y)
  have h2 := carre_positif (y - z)
  have h3 := carre_positif (z - x)
  grind

end Parcours.Classiques

#verifier
