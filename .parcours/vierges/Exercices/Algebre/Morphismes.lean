import Exercices.Algebre.Inverses

/-!
# Morphismes de groupes

Un **morphisme** `f : G → H` respecte la multiplication : `f (a * b) = f a * f b`.
On n'a pas besoin de supposer qu'il respecte `1` et `⁻¹` : ça se **déduit** !

Exemple : `exp : (ℝ, +) → (ℝ*, ×)` car `exp (a + b) = exp a × exp b`.

## À prouver
1. `map_one : f 1 = 1`
2. `map_inv : f a⁻¹ = (f a)⁻¹`

---
*Exercice* `Algebre.Morphismes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.Morphismes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G H : Type} [Groupe G] [Groupe H]

structure Morphisme (G H : Type) [Groupe G] [Groupe H] where
  f : G → H
  map_mul : ∀ a b, f (a * b) = f a * f b

theorem Morphisme.map_one (φ : Morphisme G H) : φ.f 1 = 1 := by
  sorry

theorem Morphisme.map_inv (φ : Morphisme G H) (a : G) : φ.f a⁻¹ = (φ.f a)⁻¹ := by
  sorry

end Parcours.Algebre

#verifier
