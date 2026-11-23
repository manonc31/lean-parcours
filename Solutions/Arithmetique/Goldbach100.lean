/- @parcours
titre: Goldbach, vérifié
difficulte: 1
requiert: Arithmetique.TestPrimalite
indice: Des calculs : `decide +kernel`.
-/
import Solutions.Arithmetique.Definitions
import Solutions.Listes.Pont

/-!
# Goldbach, vérifié

La conjecture de Goldbach (1742) : tout nombre pair supérieur à 2 est la somme de deux nombres
premiers (`4 = 2 + 2`, `28 = 5 + 23`…). Elle est vérifiée par ordinateur jusqu'à `4 × 10¹⁸`, mais
**personne** ne sait la prouver (voir la branche Problèmes ouverts). Vérifions-la jusqu'à 200, et
regardons les nombres premiers jumeaux.

## À prouver
1. `goldbach_200` : tout pair de 4 à 200 est somme de deux premiers.
2. `jumeaux_100` : les couples de premiers jumeaux `(p, p + 2)` sous 100.

## Ressources
- [Conjecture de Goldbach (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Goldbach)
-/

namespace Parcours.Arith

def premierB (p : Nat) : Bool := 2 ≤ p && (List.range p).all fun d => d < 2 || p % d != 0

def decomposable (n : Nat) : Bool := (List.range n).any fun p => premierB p && premierB (n - p)

theorem goldbach_200 : ∀ k, k < 99 → decomposable (2 * k + 4) = true := by -- @exo
  decide +kernel

theorem jumeaux_100 : ((List.range 100).filter fun p => premierB p && premierB (p + 2)) =
    [3, 5, 11, 17, 29, 41, 59, 71] := by -- @exo
  decide +kernel

end Parcours.Arith

#verifier
