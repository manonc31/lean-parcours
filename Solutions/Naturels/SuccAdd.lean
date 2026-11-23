/- @parcours
titre: Successeur à gauche
difficulte: 2
indice: Récurrence sur `b` (pas sur `a` !).
indice: Cas `succ` : le but est `succ a + succ b = succ (a + succ b)`. Réécris avec `add_succ` (plusieurs fois) puis `ih`.
-/
import Solutions.Naturels.ZeroAdd

/-!
# Successeur à gauche

Par définition, `a + succ b = succ (a + b)`. Prouve la version « à gauche ».

## À prouver
`succ_add (a b : ℕ) : succ a + b = succ (a + b)`
-/

namespace Parcours.ℕ

theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by -- @exo
  induction b with
  | zero => rfl
  | succ b ih => rw [add_succ, ih, add_succ]

end Parcours.ℕ

#verifier
