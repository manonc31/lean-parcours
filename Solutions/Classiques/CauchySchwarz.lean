/- @parcours
titre: L'inégalité de Cauchy-Schwarz
difficulte: 3
celebre: 78
requiert: Olympiades.AMGM
indice: Un carré est positif : sépare `x ≥ 0` et `x ≤ 0` (`Int.le_total`), puis `Int.mul_nonneg`. Pour `x ≤ 0`, passe par `-x` (`Int.neg_mul_neg`).
indice: Pour Cauchy-Schwarz : `carre_positif (a * d - b * c)`, puis `grind` trouve la combinaison.
-/
import Solutions.Arithmetique.Definitions

/-!
# L'inégalité de Cauchy-Schwarz

## Se le représenter
Pour deux vecteurs `(a, b)` et `(c, d)` du plan, le produit scalaire est plus petit que le produit des
longueurs : `(ac + bd)² ≤ (a² + b²)(c² + d²)`. L'identité de Lagrange explique tout :
la différence vaut exactement `(ad − bc)²`, un carré, donc positive.

## À prouver
`carre_positif (x : Int) : 0 ≤ x * x`, puis `cauchy_schwarz (a b c d : Int) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)`

## Ressources
- [Inégalité de Cauchy-Schwarz (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_de_Cauchy-Schwarz)
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem carre_positif (x : Int) : 0 ≤ x * x := by -- @exo
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

theorem cauchy_schwarz (a b c d : Int) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by -- @exo
  have h := carre_positif (a * d - b * c)
  grind

end Parcours.Classiques

#verifier
