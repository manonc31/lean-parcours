/- @parcours
titre: La factorielle bat le carré
difficulte: 3
requiert: Recurrence.Croissance
indice: Écris `n = k + 4` et fais une récurrence sur `k`.
indice: `(n+1)! = (n+1)·n! ≥ (n+1)·n² ≥ (n+1)·(n+1)` car `n² ≥ n + 1`. `Nat.mul_le_mul_left` pour multiplier des inégalités.
-/
import Solutions.Recurrence.Definitions

/-!
# La factorielle bat le carré

## Se le représenter
`4! = 24 ≥ 16 = 4²`, `5! = 120 ≥ 25`… et ensuite chaque étape multiplie la factorielle par `n + 1`,
alors que le carré grandit beaucoup moins.

## À prouver
`fact_carre (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ fact n`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem fact_carre (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ fact n := by -- @exo
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  clear h
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by omega, fact_succ]
    have h1 : (k + 4 + 1) * (k + 4) ^ 2 ≤ (k + 4 + 1) * fact (k + 4) := Nat.mul_le_mul_left _ ih
    have h2 : k + 4 + 1 ≤ (k + 4) ^ 2 := by grind
    have h3 : (k + 4 + 1) * (k + 4 + 1) ≤ (k + 4 + 1) * (k + 4) ^ 2 := Nat.mul_le_mul_left _ h2
    rw [Nat.pow_two]
    omega

end Parcours.Classiques

#verifier
