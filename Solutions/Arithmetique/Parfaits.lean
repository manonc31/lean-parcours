/- @parcours
titre: Nombres parfaits et amicaux
difficulte: 1
requiert: Arithmetique.DiviseBase
indice: Des calculs : `decide` / `decide +kernel`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Nombres parfaits et amicaux

Un nombre est **parfait** s'il est égal à la somme de ses diviseurs stricts : `6 = 1 + 2 + 3`,
`28 = 1 + 2 + 4 + 7 + 14`. Les Grecs n'en connaissaient que quatre : 6, 28, 496, 8128. Tous sont de
la forme `2^(p−1) × (2^p − 1)` (Euclide). On ne sait toujours pas s'il existe un parfait impair !

`220` et `284` sont **amicaux** : chacun est la somme des diviseurs stricts de l'autre.

## À prouver
1. `quatre_parfaits`, `pas_d_autre` (sous 100 : seulement 6 et 28)
2. `amicaux`
3. `forme_euclide`

## Ressources
- [Nombre parfait (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_parfait)
-/

namespace Parcours.Arith

def diviseursStricts (n : Nat) : List Nat := (List.range n).filter fun d => 0 < d && n % d == 0

def parfait (n : Nat) : Bool := 0 < n && (diviseursStricts n).sum == n

theorem quatre_parfaits : parfait 6 && parfait 28 && parfait 496 && parfait 8128 = true := by -- @exo
  decide +kernel

theorem pas_d_autre : (List.range 100).filter parfait = [6, 28] := by -- @exo
  decide +kernel

theorem amicaux : (diviseursStricts 220).sum = 284 ∧ (diviseursStricts 284).sum = 220 := by -- @exo
  decide

theorem forme_euclide : 6 = 2 ^ 1 * (2 ^ 2 - 1) ∧ 28 = 2 ^ 2 * (2 ^ 3 - 1) ∧
    496 = 2 ^ 4 * (2 ^ 5 - 1) ∧ 8128 = 2 ^ 6 * (2 ^ 7 - 1) := by -- @exo
  decide

end Parcours.Arith

#verifier
