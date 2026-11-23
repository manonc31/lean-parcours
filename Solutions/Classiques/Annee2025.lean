/- @parcours
titre: 2025, une année remarquable
difficulte: 1
requiert: Recurrence.Cubes
indice: Des calculs : `decide`.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# 2025, une année remarquable

2025 est un carré : `45²`. C'est aussi un nombre de Kaprekar : `20 + 25 = 45`. Et
`2025 = (1 + 2 + ⋯ + 9)² = 1³ + 2³ + ⋯ + 9³` (Nicomaque !). La prochaine année carrée sera 2116.

## À prouver
`carre`, `kaprekar`, `nicomaque`, et `prochaine` (aucun carré entre 2025 et 2116).
-/

namespace Parcours.Classiques

theorem carre : 2025 = 45 ^ 2 := by -- @exo
  decide

theorem kaprekar : 2025 / 100 + 2025 % 100 = 45 := by -- @exo
  decide

theorem nicomaque : ((List.range 10).sum) ^ 2 = 2025 ∧ ((List.range 10).map (· ^ 3)).sum = 2025 := by -- @exo
  decide

theorem prochaine : 2116 = 46 ^ 2 ∧ ∀ k, k < 100 → k ^ 2 ≤ 2025 ∨ 2116 ≤ k ^ 2 := by -- @exo
  decide

end Parcours.Classiques

#verifier
