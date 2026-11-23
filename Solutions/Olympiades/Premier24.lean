/- @parcours
titre: p² − 1 est divisible par 24
difficulte: 4
requiert: Arithmetique.LemmeEuclide, Olympiades.Parite
indice: Un nombre premier `p ≥ 5` n'est divisible ni par 2 ni par 3 : sinon `2 ∣ p` donnerait `2 = 1 ∨ 2 = p` (`hp.2`).
indice: Donc `p % 24` vaut 1, 5, 7, 11, 13, 17, 19 ou 23. Dans chaque cas, `(p * p) % 24 = 1` (`Nat.mul_mod`).
indice: Pour obtenir la liste des cas : `have : p % 24 = 1 ∨ p % 24 = 5 ∨ … := by omega` (avec les hypothèses `p % 2 ≠ 0` et `p % 3 ≠ 0`).
indice: Enfin, `24 ∣ p * p - 1` : témoin `(p * p - 1) / 24`, et `omega`.
-/
import Solutions.Arithmetique.Definitions

/-!
# p² − 1 est divisible par 24

> Pour tout nombre premier `p ≥ 5`, `24` divise `p² − 1`.

`5² − 1 = 24`, `7² − 1 = 48`, `11² − 1 = 120`, `13² − 1 = 168`… Un classique des concours.

## À prouver
`premier_carre (hp : Premier p) (h5 : 5 ≤ p) : 24 ∣ p * p - 1`
-/

namespace Parcours.Olymp

open Parcours.Arith

theorem premier_carre {p : Nat} (hp : Premier p) (h5 : 5 ≤ p) : 24 ∣ p * p - 1 := by -- @exo
  have h2 : p % 2 ≠ 0 := by
    intro h
    rcases hp.2 2 ⟨p / 2, by omega⟩ with h' | h' <;> omega
  have h3 : p % 3 ≠ 0 := by
    intro h
    rcases hp.2 3 ⟨p / 3, by omega⟩ with h' | h' <;> omega
  have hcarre : (p * p) % 24 = 1 := by
    have : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨
        p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> simp [Nat.mul_mod, h]
  have hpos : 1 ≤ p * p := Nat.mul_pos (by omega) (by omega)
  exact ⟨(p * p - 1) / 24, by omega⟩

end Parcours.Olymp

#verifier
