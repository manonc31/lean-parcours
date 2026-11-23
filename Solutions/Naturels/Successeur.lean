/- @parcours
titre: Successeur et « + 1 »
difficulte: 1
indice: `succ_eq_add_one` est vrai par définition : `rfl` suffit ! (Lean déplie `n + 1 = n + succ 0 = succ (n + 0) = succ n`.)
indice: Pour `one_add_eq_succ`, `rw [one_eq_succ_zero, succ_add, zero_add]`.
-/
import Solutions.Naturels.SuccAdd

/-!
# Successeur et « + 1 »

`succ n` et `n + 1` désignent le même entier. Mais pour Lean ce sont deux **expressions**
différentes : l'une est un constructeur, l'autre une addition. Quand c'est vrai « par calcul »,
`rfl` le voit. Sinon, il faut réécrire.

## À prouver
1. `succ_eq_add_one (n : ℕ) : succ n = n + 1`
2. `one_add_eq_succ (n : ℕ) : 1 + n = succ n`

## Rappel
`one_eq_succ_zero : 1 = succ 0`, `succ_add`, `zero_add`.
-/

namespace Parcours.ℕ

theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 := by -- @exo
  rfl

theorem one_add_eq_succ (n : ℕ) : 1 + n = succ n := by -- @exo
  rw [one_eq_succ_zero, succ_add, zero_add]

end Parcours.ℕ

#verifier
