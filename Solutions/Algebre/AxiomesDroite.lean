/- @parcours
titre: Les axiomes à droite
difficulte: 3
indice: `mul_inv` : montre que `x := a * a⁻¹` vérifie `x * x = x`, puis `idempotent`.
indice: `(a * a⁻¹) * (a * a⁻¹) = a * (a⁻¹ * (a * a⁻¹)) = a * ((a⁻¹ * a) * a⁻¹) = a * (1 * a⁻¹) = a * a⁻¹`. Les `Groupe.mul_assoc` sont à placer avec soin.
indice: `mul_one` : `a * 1 = a * (a⁻¹ * a) = (a * a⁻¹) * a = 1 * a = a`.
-/
import Solutions.Algebre.Simplification

/-!
# Les axiomes à droite

On a seulement supposé `1 * a = a` et `a⁻¹ * a = 1`. Montre que l'on a aussi, gratuitement :
`a * a⁻¹ = 1` et `a * 1 = a`. C'est un grand classique (et un petit casse-tête).

## À prouver
1. `mul_inv (a : G) : a * a⁻¹ = 1`
2. `mul_one (a : G) : a * 1 = a`
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem mul_inv (a : G) : a * a⁻¹ = 1 := by -- @exo
  apply idempotent
  calc a * a⁻¹ * (a * a⁻¹) = a * (a⁻¹ * (a * a⁻¹)) := Groupe.mul_assoc _ _ _
    _ = a * (a⁻¹ * a * a⁻¹) := by rw [Groupe.mul_assoc a⁻¹ a a⁻¹]
    _ = a * a⁻¹ := by rw [Groupe.inv_mul, Groupe.one_mul]

theorem mul_one (a : G) : a * 1 = a := by -- @exo
  calc a * 1 = a * (a⁻¹ * a) := by rw [Groupe.inv_mul]
    _ = a * a⁻¹ * a := (Groupe.mul_assoc _ _ _).symm
    _ = a := by rw [mul_inv, Groupe.one_mul]

end Parcours.Algebre

#verifier
