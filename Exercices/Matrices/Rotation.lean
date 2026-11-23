import Exercices.Matrices.Definitions

/-!
# Le quart de tour

La matrice `R = ((0, −1), (1, 0))` fait tourner le plan d'un quart de tour. Quatre quarts de tour
font un tour complet : `R⁴ = I`. Et `R² = −I` : un demi-tour change chaque vecteur en son opposé,
comme `i² = −1` pour les nombres complexes !

Une matrice **nilpotente** : `N = ((0, 1), (0, 0))` n'est pas nulle, mais `N² = 0`.

## À prouver
`demi_tour`, `tour_complet`, `nilpotente`, `det_rotation`.

---
*Exercice* `Matrices.Rotation` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Matrices.Rotation` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Matrices

open M2

def R : M2 := ⟨0, -1, 1, 0⟩
def N : M2 := ⟨0, 1, 0, 0⟩

theorem demi_tour : R * R = ⟨-1, 0, 0, -1⟩ := by
  sorry

theorem tour_complet : puiss R 4 = id2 := by
  sorry

theorem nilpotente : N ≠ ⟨0, 0, 0, 0⟩ ∧ N * N = ⟨0, 0, 0, 0⟩ := by
  sorry

theorem det_rotation : det R = 1 := by
  sorry

end Parcours.Matrices

#verifier
