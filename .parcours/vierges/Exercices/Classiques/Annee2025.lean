import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# 2025, une année remarquable

2025 est un carré : `45²`. C'est aussi un nombre de Kaprekar : `20 + 25 = 45`. Et
`2025 = (1 + 2 + ⋯ + 9)² = 1³ + 2³ + ⋯ + 9³` (Nicomaque !). La prochaine année carrée sera 2116.

## À prouver
`carre`, `kaprekar`, `nicomaque`, et `prochaine` (aucun carré entre 2025 et 2116).

---
*Exercice* `Classiques.Annee2025` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.Annee2025` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

theorem carre : 2025 = 45 ^ 2 := by
  sorry

theorem kaprekar : 2025 / 100 + 2025 % 100 = 45 := by
  sorry

theorem nicomaque : ((List.range 10).sum) ^ 2 = 2025 ∧ ((List.range 10).map (· ^ 3)).sum = 2025 := by
  sorry

theorem prochaine : 2116 = 46 ^ 2 ∧ ∀ k, k < 100 → k ^ 2 ≤ 2025 ∨ 2116 ≤ k ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
