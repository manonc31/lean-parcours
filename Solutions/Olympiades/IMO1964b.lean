/- @parcours
titre: IMO 1964, problème 1 (b)
difficulte: 2
requiert: Olympiades.IMO1964
indice: Réutilise `reste_puissance_deux` (la première partie), puis `repeat' split at h` et `omega`.
-/
import Solutions.Olympiades.IMO1964

/-!
# IMO 1964, problème 1 (b)

> Montrer qu'il n'existe aucun entier `n` tel que `2ⁿ + 1` soit divisible par 7.

Les restes de `2ⁿ` modulo 7 sont `1, 2, 4` : en ajoutant 1, on obtient `2, 3, 5`, jamais 0.

## À prouver
`imo1964b : (2 ^ n + 1) % 7 ≠ 0`
-/

namespace Parcours.Olymp

theorem imo1964b (n : Nat) : (2 ^ n + 1) % 7 ≠ 0 := by -- @exo
  have h := reste_puissance_deux n
  repeat' split at h
  all_goals omega

end Parcours.Olymp

#verifier
