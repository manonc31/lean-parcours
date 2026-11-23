/- @parcours
titre: Deux carrés qui diffèrent de 2
difficulte: 2
requiert: Olympiades.Parite
indice: Lemme : pour tout `z`, `z * z % 4` vaut 0 ou 1 (quatre cas sur `z % 4`, `Nat.mul_mod`).
indice: Applique-le à `x` et `y`, puis `omega` avec `h`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Deux carrés qui diffèrent de 2

Deux carrés parfaits ne diffèrent **jamais** de 2. L'astuce : regarder modulo 4. Un carré vaut
toujours 0 ou 1 modulo 4.

## À prouver
`difference_carres : ¬∃ x y : Nat, x * x = y * y + 2`
-/

namespace Parcours.Olymp

theorem difference_carres : ¬∃ x y : Nat, x * x = y * y + 2 := by -- @exo
  rintro ⟨x, y, h⟩
  have carre : ∀ z : Nat, z * z % 4 = 0 ∨ z * z % 4 = 1 := by
    intro z
    have : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    rcases this with hz | hz | hz | hz <;> simp [Nat.mul_mod, hz]
  have hx := carre x
  have hy := carre y
  omega

end Parcours.Olymp

#verifier
