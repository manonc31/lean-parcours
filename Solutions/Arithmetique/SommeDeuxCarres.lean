/- @parcours
titre: Somme de deux carrés modulo 4
difficulte: 2
requiert: Arithmetique.Congruences
indice: Un carré vaut 0 ou 1 modulo 4 (quatre cas sur le reste, `Nat.mul_mod`).
indice: Puis `omega`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Somme de deux carrés modulo 4

Une somme de deux carrés n'est jamais de la forme `4k + 3`. Donc `3, 7, 11, 19, 23…` ne sont pas sommes
de deux carrés. (Fermat a montré que pour les premiers, c'est même une équivalence : voir le boss des deux carrés.)

## À prouver
`somme_deux_carres (a b : Nat) : (a * a + b * b) % 4 ≠ 3`
-/

namespace Parcours.Arith

theorem somme_deux_carres (a b : Nat) : (a * a + b * b) % 4 ≠ 3 := by -- @exo
  have carre : ∀ z : Nat, z * z % 4 = 0 ∨ z * z % 4 = 1 := by
    intro z
    have : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    rcases this with hz | hz | hz | hz <;> simp [Nat.mul_mod, hz]
  have ha := carre a
  have hb := carre b
  omega

end Parcours.Arith

#verifier
