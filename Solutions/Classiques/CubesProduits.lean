/- @parcours
titre: a³ + b³ ≥ a²b + ab²
difficulte: 2
requiert: Classiques.SommeCarresProduits
indice: `(a + b)(a − b)² ≥ 0` : `Int.mul_nonneg (Int.add_nonneg ha hb) (carre_positif (a - b))`.
-/
import Solutions.Classiques.CauchySchwarz

/-!
# a³ + b³ ≥ a²b + ab²

## Se le représenter
Pour `a, b ≥ 0` : `a³ + b³ − a²b − ab² = (a + b)(a − b)²`, produit de deux nombres positifs.

## À prouver
`cubes_produits : 0 ≤ a → 0 ≤ b → a ^ 2 * b + a * b ^ 2 ≤ a ^ 3 + b ^ 3`
-/

namespace Parcours.Classiques

theorem cubes_produits (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * b + a * b ^ 2 ≤ a ^ 3 + b ^ 3 := by -- @exo
  have h := Int.mul_nonneg (Int.add_nonneg ha hb) (carre_positif (a - b))
  grind

end Parcours.Classiques

#verifier
