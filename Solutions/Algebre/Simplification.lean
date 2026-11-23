/- @parcours
titre: Simplifier dans un groupe
difficulte: 2
indice: `mul_gauche_simpl` : multiplie à gauche par `a⁻¹`. Concrètement : `calc b = 1 * b := (Groupe.one_mul b).symm` puis `_ = a⁻¹ * a * b`, puis `_ = a⁻¹ * (a * b)`, puis `rw [h]` et on remonte.
indice: `idempotent` : si `x * x = x`, alors `x = 1 * x = (x⁻¹ * x) * x = x⁻¹ * (x * x) = x⁻¹ * x = 1`.
-/
import Solutions.Algebre.Definitions

/-!
# Simplifier dans un groupe

Dans un groupe, on peut « simplifier » à gauche : si `a * b = a * c`, alors `b = c`.
(Faux dans `(ℕ, ×)` avec `a = 0` : ce n'est pas un groupe !)

## À prouver
1. `mul_gauche_simpl : a * b = a * c → b = c`
2. `idempotent : x * x = x → x = 1`
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem mul_gauche_simpl {a b c : G} (h : a * b = a * c) : b = c := by -- @exo
  calc b = 1 * b := (Groupe.one_mul b).symm
    _ = a⁻¹ * a * b := by rw [Groupe.inv_mul]
    _ = a⁻¹ * (a * b) := Groupe.mul_assoc _ _ _
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = a⁻¹ * a * c := (Groupe.mul_assoc _ _ _).symm
    _ = c := by rw [Groupe.inv_mul, Groupe.one_mul]

theorem idempotent {x : G} (h : x * x = x) : x = 1 := by -- @exo
  calc x = 1 * x := (Groupe.one_mul x).symm
    _ = x⁻¹ * x * x := by rw [Groupe.inv_mul]
    _ = x⁻¹ * (x * x) := Groupe.mul_assoc _ _ _
    _ = x⁻¹ * x := by rw [h]
    _ = 1 := Groupe.inv_mul x

end Parcours.Algebre

#verifier
