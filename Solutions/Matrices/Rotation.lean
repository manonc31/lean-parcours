/- @parcours
titre: Le quart de tour
difficulte: 1
requiert: Matrices.Associativite
indice: Des calculs sur des matrices concrètes : `decide`.
-/
import Solutions.Matrices.Definitions

/-!
# Le quart de tour

La matrice `R = ((0, −1), (1, 0))` fait tourner le plan d'un quart de tour. Quatre quarts de tour
font un tour complet : `R⁴ = I`. Et `R² = −I` : un demi-tour change chaque vecteur en son opposé,
comme `i² = −1` pour les nombres complexes !

Une matrice **nilpotente** : `N = ((0, 1), (0, 0))` n'est pas nulle, mais `N² = 0`.

## À prouver
`demi_tour`, `tour_complet`, `nilpotente`, `det_rotation`.
-/

namespace Parcours.Matrices

open M2

def R : M2 := ⟨0, -1, 1, 0⟩
def N : M2 := ⟨0, 1, 0, 0⟩

theorem demi_tour : R * R = ⟨-1, 0, 0, -1⟩ := by -- @exo
  decide

theorem tour_complet : puiss R 4 = id2 := by -- @exo
  decide

theorem nilpotente : N ≠ ⟨0, 0, 0, 0⟩ ∧ N * N = ⟨0, 0, 0, 0⟩ := by -- @exo
  decide

theorem det_rotation : det R = 1 := by -- @exo
  decide

end Parcours.Matrices

#verifier
