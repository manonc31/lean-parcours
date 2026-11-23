/- @parcours
celebre: 68
titre: La somme de Gauss
difficulte: 2
indice: Récurrence sur `n`. Cas `zero` : `rfl`.
indice: Cas `succ` : `rw [somme_succ]`, puis il faut montrer `2 * (S + (n+1)) = (n+1) * (n+2)` sachant `ih : 2 * S = n * (n+1)`. `grind` le fait. (Ou à la main : `Nat.mul_add`, `Nat.add_mul`, puis `omega`.)
-/
import Solutions.Recurrence.Definitions

/-!
# La somme de Gauss

La légende dit que le petit Gauss, à 9 ans, a calculé `1 + 2 + ⋯ + 100 = 5050` en quelques secondes.
`0 + 1 + 2 + ⋯ + n = n(n+1)/2`.

## À prouver
`gauss (n : Nat) : 2 * somme (fun i => i) (n + 1) = n * (n + 1)`

## Ressources
- [Nombre triangulaire (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_triangulaire)
-/

namespace Parcours.Recurrence

theorem gauss (n : Nat) : 2 * somme (fun i => i) (n + 1) = n * (n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ]
    grind

end Parcours.Recurrence

#verifier
