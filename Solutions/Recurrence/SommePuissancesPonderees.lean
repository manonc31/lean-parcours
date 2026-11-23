/- @parcours
titre: Une somme pondérée
difficulte: 3
requiert: Recurrence.Geometrique
indice: Récurrence ; `somme_succ` et `Nat.pow_succ`, puis `grind` avec l'hypothèse de récurrence.
-/
import Solutions.Recurrence.Definitions

/-!
# Une somme pondérée

`Σ k·2ᵏ` pour `k` de 0 à `n` vaut `(n − 1)·2ⁿ⁺¹ + 2`. Pour éviter la soustraction, on écrit :
`Σ k·2ᵏ + 2ⁿ⁺¹ = n·2ⁿ⁺¹ + 2`.

## À prouver
`somme_ponderee (n : Nat) : somme (fun k => k * 2 ^ k) (n + 1) + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2`
-/

namespace Parcours.Recurrence

theorem somme_ponderee (n : Nat) :
    somme (fun k => k * 2 ^ k) (n + 1) + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.pow_succ 2 (n + 1)]
    grind

end Parcours.Recurrence

#verifier
