/- @parcours
titre: Calculs avec les inverses
difficulte: 2
indice: Chaque preuve : utilise `inverse_unique`, en vérifiant qu'un candidat est bien un inverse.
indice: `inv_inv` : `a⁻¹ * a = 1`, donc `a = (a⁻¹)⁻¹`. Attention au sens (`.symm`).
indice: `mul_inv_rev` : montre `(a * b) * (b⁻¹ * a⁻¹) = 1` en réassociant, puis `inverse_unique`.
-/
import Solutions.Algebre.Unicite

/-!
# Calculs avec les inverses

« Pour défaire une action composée, on défait les actions dans l'ordre inverse » :
pour enlever chaussettes puis chaussures, on enlève d'abord les chaussures !

## À prouver
1. `inv_inv : (a⁻¹)⁻¹ = a`
2. `inv_one : (1 : G)⁻¹ = 1`
3. `mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹`
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by -- @exo
  exact (inverse_unique (Groupe.inv_mul a)).symm

theorem inv_one : (1 : G)⁻¹ = 1 := by -- @exo
  exact (inverse_unique (Groupe.one_mul (1 : G))).symm

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by -- @exo
  apply Eq.symm
  apply inverse_unique
  calc a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) := Groupe.mul_assoc _ _ _
    _ = a * (b * b⁻¹ * a⁻¹) := by rw [Groupe.mul_assoc b]
    _ = 1 := by rw [mul_inv, Groupe.one_mul, mul_inv]

end Parcours.Algebre

#verifier
