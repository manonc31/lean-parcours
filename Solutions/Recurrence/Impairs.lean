/- @parcours
titre: La somme des impairs
difficulte: 2
indice: Récurrence sur `n`, `rw [somme_succ, ih]`.
indice: Il reste `n ^ 2 + (2 * n + 1) = (n + 1) ^ 2` : `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# La somme des impairs

`1 + 3 + 5 + ⋯ + (2n - 1) = n²`. Un dessin le montre : des équerres qui s'emboîtent en carré.

## À prouver
`somme_impairs (n : Nat) : somme (fun i => 2 * i + 1) n = n ^ 2`
-/

namespace Parcours.Recurrence

theorem somme_impairs (n : Nat) : somme (fun i => 2 * i + 1) n = n ^ 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, ih]
    grind

end Parcours.Recurrence

#verifier
