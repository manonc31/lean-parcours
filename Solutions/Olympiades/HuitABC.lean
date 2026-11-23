/- @parcours
titre: (a + b)(b + c)(c + a) ≥ 8abc
difficulte: 3
requiert: Classiques.CauchySchwarz
indice: Trois termes positifs : `Int.mul_nonneg ha (carre_positif (b - c))`, etc.
indice: Avec ces trois faits, `grind` conclut.
-/
import Solutions.Classiques.CauchySchwarz

/-!
# (a + b)(b + c)(c + a) ≥ 8abc

Pour `a, b, c ≥ 0` : `(a + b)(b + c)(c + a) ≥ 8abc`. On peut le voir avec AM-GM
(`a + b ≥ 2√ab`…), mais il y a plus simple : la différence vaut
`a(b − c)² + b(c − a)² + c(a − b)²`, une somme de termes positifs.

## À prouver
`huit_abc : 0 ≤ a → 0 ≤ b → 0 ≤ c → 8 * a * b * c ≤ (a + b) * (b + c) * (c + a)`
-/

namespace Parcours.Olymp

theorem huit_abc (a b c : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    8 * a * b * c ≤ (a + b) * (b + c) * (c + a) := by -- @exo
  have h1 := Int.mul_nonneg ha (Parcours.Classiques.carre_positif (b - c))
  have h2 := Int.mul_nonneg hb (Parcours.Classiques.carre_positif (c - a))
  have h3 := Int.mul_nonneg hc (Parcours.Classiques.carre_positif (a - b))
  grind

end Parcours.Olymp

#verifier
