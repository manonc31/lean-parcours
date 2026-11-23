/- @parcours
titre: Le carré d'un produit
difficulte: 3
requiert: Algebre.Inverses
indice: Sens `→` : réassocie pour faire apparaître `a * (…)` des deux côtés, simplifie par `a` à gauche (`mul_gauche_simpl`), puis par `b` à droite.
indice: Pour simplifier à droite, prouve d'abord `x * z = y * z → x = y` (multiplie par `z⁻¹`).
indice: Sens `←` : réécris `b * a` en `a * b` au bon endroit (`← h`) et réassocie.
-/
import Solutions.Algebre.Inverses

/-!
# Le carré d'un produit

Dans un groupe, `(ab)² = a²b²` si et seulement si `a` et `b` **commutent**. (Dans un groupe non
commutatif, l'identité `(ab)² = a²b²` est donc fausse en général !)

## À prouver
`carre_produit : a * b * (a * b) = a * a * (b * b) ↔ a * b = b * a`
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem carre_produit (a b : G) : a * b * (a * b) = a * a * (b * b) ↔ a * b = b * a := by -- @exo
  have simpl_droite : ∀ x y z : G, x * z = y * z → x = y := by
    intro x y z h
    calc x = x * z * z⁻¹ := by rw [Groupe.mul_assoc, mul_inv, mul_one]
      _ = y * z * z⁻¹ := by rw [h]
      _ = y := by rw [Groupe.mul_assoc, mul_inv, mul_one]
  constructor
  · intro h
    rw [Groupe.mul_assoc, Groupe.mul_assoc a a] at h
    have h2 := mul_gauche_simpl h
    rw [← Groupe.mul_assoc, ← Groupe.mul_assoc a b b] at h2
    exact (simpl_droite _ _ _ h2).symm
  · intro h
    rw [Groupe.mul_assoc, ← Groupe.mul_assoc b a b, ← h, Groupe.mul_assoc a b b, ← Groupe.mul_assoc]

end Parcours.Algebre

#verifier
