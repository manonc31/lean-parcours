/- @parcours
titre: Quand tout élément est son propre inverse
difficulte: 3
indice: De `x * x = 1`, déduis `x = x⁻¹` (avec `inverse_unique`).
indice: Alors `a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹ = b * a`.
-/
import Solutions.Algebre.Inverses

/-!
# Quand tout élément est son propre inverse

Si `x * x = 1` pour **tout** `x`, alors le groupe est **commutatif**. Joli, et surprenant !

## À prouver
`commutatif_si_carre_un (h : ∀ x : G, x * x = 1) (a b : G) : a * b = b * a`
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem commutatif_si_carre_un (h : ∀ x : G, x * x = 1) (a b : G) : a * b = b * a := by -- @exo
  have hinv : ∀ x : G, x⁻¹ = x := fun x => (inverse_unique (h x)).symm
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv, hinv]

end Parcours.Algebre

#verifier
