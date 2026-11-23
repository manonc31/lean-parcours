/- @parcours
titre: Commutativité de l'addition
difficulte: 2
indice: Récurrence sur `b`.
indice: Cas `zero` : `a + 0 = 0 + a`. Tu as `add_zero` et `zero_add`.
indice: Cas `succ` : `rw [add_succ, ih, succ_add]`.
-/
import Solutions.Naturels.SuccAdd

/-!
# Commutativité de l'addition

Le grand classique : `a + b = b + a`. Dans la bibliothèque de Lean c'est une ligne
(`Nat.add_comm`)… mais ici, c'est **ton** ℕ, et il n'y a que **tes** théorèmes.

## À prouver
`add_comm (a b : ℕ) : a + b = b + a`

## Tes outils
`add_zero`, `add_succ`, `zero_add`, `succ_add`.
-/

namespace Parcours.ℕ

theorem add_comm (a b : ℕ) : a + b = b + a := by -- @exo
  induction b with
  | zero => rw [add_zero, zero_add]
  | succ b ih => rw [add_succ, ih, succ_add]

end Parcours.ℕ

#verifier
