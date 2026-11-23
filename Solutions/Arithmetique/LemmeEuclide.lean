/- @parcours
titre: Le lemme d'Euclide
difficulte: 3
indice: `pgcd p a` divise `p` (`pgcd_divise`), donc vaut `1` ou `p` (car `p` est premier : `hp.2`).
indice: S'il vaut `p`, alors `p ∣ a`. S'il vaut `1`, le lemme de Gauss donne `p ∣ b`.
-/
import Solutions.Arithmetique.LemmeGauss

/-!
# Le lemme d'Euclide

> Si un nombre premier divise un produit, il divise l'un des facteurs.

C'est la propriété fondamentale des nombres premiers (Euclide, *Éléments*, livre VII, ~300 av. J.-C.).

## À prouver
`premier_divise_mul : Premier p → p ∣ a * b → p ∣ a ∨ p ∣ b`

## Ressources
- [Lemme d'Euclide (Wikipédia)](https://fr.wikipedia.org/wiki/Lemme_d%27Euclide)
-/

namespace Parcours.Arith

theorem premier_divise_mul {p a b : Nat} (hp : Premier p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by -- @exo
  rcases hp.2 (pgcd p a) (pgcd_divise p a).1 with h1 | h1
  · right
    exact lemme_gauss h h1
  · left
    rw [← h1]
    exact (pgcd_divise p a).2

end Parcours.Arith

#verifier
