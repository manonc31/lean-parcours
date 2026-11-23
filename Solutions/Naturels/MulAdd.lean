/- @parcours
titre: Distributivité
difficulte: 3
indice: Récurrence sur `c`. Le cas `zero` est vrai par définition (`rfl`).
indice: Cas `succ` : `rw [add_succ, mul_succ, ih, mul_succ, add_assoc]`.
-/
import Solutions.Naturels.Multiplication
import Solutions.Naturels.AddAssoc

/-!
# Distributivité de × sur +

`a × (b + c) = a × b + a × c`. Le pont entre l'addition et la multiplication.

## À prouver
`mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c`
-/

namespace Parcours.ℕ

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by -- @exo
  induction c with
  | zero => rfl
  | succ c ih => rw [add_succ, mul_succ, ih, mul_succ, add_assoc]

end Parcours.ℕ

#verifier
