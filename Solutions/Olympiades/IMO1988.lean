/- @parcours
titre: IMO 1988, problème 6
difficulte: 5
genre: boss
solution: non
requiert: Olympiades.IMO1959, Olympiades.AMGM
indice: La technique s'appelle le « saut de Viète » (*Vieta jumping*). Suppose que `k = (a² + b²)/(ab + 1)` n'est pas un carré, et prends une solution `(a, b)` avec `a + b` minimal.
indice: Pour `b` fixé, `a` est racine de `x² − k b x + (b² − k) = 0`. L'autre racine est `a' = k b − a = (b² − k)/a`. Montre que `a'` est un entier positif et que `a' < a`.
indice: C'est une descente infinie : contradiction avec la minimalité. En Lean, travaille dans `Int` pour l'autre racine.
-/
import Solutions.Arithmetique.Definitions

/-!
# 💀 IMO 1988, problème 6

> Soient `a` et `b` des entiers strictement positifs tels que `ab + 1` divise `a² + b²`.
> Montrer que `(a² + b²) / (ab + 1)` est un carré parfait.

Le problème le plus célèbre de l'histoire des Olympiades : aucun membre du jury australien qui l'a
proposé ne savait le résoudre, ni les meilleurs théoriciens des nombres du pays. 11 élèves l'ont
résolu pendant l'épreuve. Un des leurs a reçu un prix spécial pour sa solution.

Boss sans solution de référence.

## À prouver
`imo1988 (ha : 0 < a) (hb : 0 < b) (h : (a * b + 1) ∣ (a ^ 2 + b ^ 2)) : ∃ k, (a ^ 2 + b ^ 2) / (a * b + 1) = k ^ 2`

## Ressources
- [Vieta jumping (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Vieta_jumping)
-/

namespace Parcours.Olymp

theorem imo1988 (a b : Nat) (ha : 0 < a) (hb : 0 < b) (h : (a * b + 1) ∣ (a ^ 2 + b ^ 2)) :
    ∃ k, (a ^ 2 + b ^ 2) / (a * b + 1) = k ^ 2 := by -- @exo
  sorry

end Parcours.Olymp

#verifier
