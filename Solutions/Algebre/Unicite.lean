/- @parcours
titre: Unicité du neutre et de l'inverse
difficulte: 2
indice: `neutre_unique` : `e = e * 1` (`mul_one`) puis `h 1`.
indice: `inverse_unique` : `b = 1 * b = (a⁻¹ * a) * b = a⁻¹ * (a * b) = a⁻¹ * 1 = a⁻¹`.
-/
import Solutions.Algebre.AxiomesDroite

/-!
# Unicité du neutre et de l'inverse

Il n'y a qu'un seul élément neutre, et chaque élément n'a qu'un seul inverse. C'est pour ça
qu'on peut dire « **le** neutre » et « **l'**inverse ».

## À prouver
1. `neutre_unique : (∀ a, e * a = a) → e = 1`
2. `inverse_unique : a * b = 1 → b = a⁻¹`
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem neutre_unique {e : G} (h : ∀ a, e * a = a) : e = 1 := by -- @exo
  rw [← mul_one e, h 1]

theorem inverse_unique {a b : G} (h : a * b = 1) : b = a⁻¹ := by -- @exo
  calc b = 1 * b := (Groupe.one_mul b).symm
    _ = a⁻¹ * a * b := by rw [Groupe.inv_mul]
    _ = a⁻¹ * (a * b) := Groupe.mul_assoc _ _ _
    _ = a⁻¹ := by rw [h, mul_one]

end Parcours.Algebre

#verifier
