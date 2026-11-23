/- @parcours
titre: Trois divise une somme de deux carrés
difficulte: 2
requiert: Olympiades.Parite
indice: Neuf cas selon les restes de `a` et `b` modulo 3, puis `simp [Nat.add_mod, Nat.mul_mod, ha, hb] at h ⊢`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Trois divise une somme de deux carrés

Si `3` divise `a² + b²`, alors `3` divise `a` et `b`. Les carrés modulo 3 valent 0 ou 1 :
pour que la somme fasse 0, il faut deux 0.

## À prouver
`trois_divise_carres : (a * a + b * b) % 3 = 0 → a % 3 = 0 ∧ b % 3 = 0`
-/

namespace Parcours.Olymp

theorem trois_divise_carres (a b : Nat) (h : (a * a + b * b) % 3 = 0) : a % 3 = 0 ∧ b % 3 = 0 := by -- @exo
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp [Nat.add_mod, Nat.mul_mod, ha, hb] at h ⊢

end Parcours.Olymp

#verifier
