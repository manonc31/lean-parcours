import Exercices.Recurrence.Definitions

/-!
# n² contre 2ⁿ

Pour `n ≥ 4`, `n² ≤ 2ⁿ` : l'exponentielle finit toujours par battre le polynôme.
(Faux pour `n = 3` : `9 > 8`.)

## À prouver
`carre_le_puissance (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ 2 ^ n`

---
*Exercice* `Recurrence.CarreEtPuissance` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.CarreEtPuissance` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem carre_le_puissance (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  sorry

end Parcours.Recurrence

#verifier
