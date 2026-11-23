/- @parcours
titre: Morphismes de groupes
difficulte: 2
indice: `map_one` : `f 1 * f 1 = f (1 * 1) = f 1`, donc `f 1 = 1` par `idempotent`.
indice: `map_inv` : `f a * f a⁻¹ = f (a * a⁻¹) = f 1 = 1`, puis `inverse_unique`.
-/
import Solutions.Algebre.Inverses

/-!
# Morphismes de groupes

Un **morphisme** `f : G → H` respecte la multiplication : `f (a * b) = f a * f b`.
On n'a pas besoin de supposer qu'il respecte `1` et `⁻¹` : ça se **déduit** !

Exemple : `exp : (ℝ, +) → (ℝ*, ×)` car `exp (a + b) = exp a × exp b`.

## À prouver
1. `map_one : f 1 = 1`
2. `map_inv : f a⁻¹ = (f a)⁻¹`
-/

namespace Parcours.Algebre

variable {G H : Type} [Groupe G] [Groupe H]

structure Morphisme (G H : Type) [Groupe G] [Groupe H] where
  f : G → H
  map_mul : ∀ a b, f (a * b) = f a * f b

theorem Morphisme.map_one (φ : Morphisme G H) : φ.f 1 = 1 := by -- @exo
  apply idempotent
  rw [← φ.map_mul, Groupe.one_mul]

theorem Morphisme.map_inv (φ : Morphisme G H) (a : G) : φ.f a⁻¹ = (φ.f a)⁻¹ := by -- @exo
  apply inverse_unique
  rw [← φ.map_mul, mul_inv, φ.map_one]

end Parcours.Algebre

#verifier
