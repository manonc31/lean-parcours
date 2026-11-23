/- @parcours
titre: La somme des carrés
difficulte: 3
indice: Récurrence, `rw [somme_succ]`, puis `grind` avec l'hypothèse de récurrence dans le contexte.
indice: Si `grind` peine, distribue d'abord : `rw [Nat.mul_add]` puis `rw [ih]`, puis `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# La somme des carrés

`0² + 1² + ⋯ + n² = n(n+1)(2n+1)/6`.

## À prouver
`somme_carres (n : Nat) : 6 * somme (fun i => i ^ 2) (n + 1) = n * (n + 1) * (2 * n + 1)`
-/

namespace Parcours.Recurrence

theorem somme_carres (n : Nat) :
    6 * somme (fun i => i ^ 2) (n + 1) = n * (n + 1) * (2 * n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.mul_add, ih]
    grind

end Parcours.Recurrence

#verifier
