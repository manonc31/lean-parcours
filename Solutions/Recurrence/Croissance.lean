/- @parcours
titre: Qui grandit le plus vite ?
difficulte: 3
indice: `lt_deux_pow` : récurrence ; `Nat.pow_succ` puis `omega`.
indice: `deux_pow_le_fact` : récurrence ; `fact (n + 2) = (n + 2) * fact (n + 1)` et `2 ^ (n + 1) = 2 ^ n * 2`. Comme `n + 2 ≥ 2`, ça marche (`Nat.mul_le_mul`).
indice: `fact_le_pow` : récurrence ; `(n+1)! = (n+1) · n! ≤ (n+1) · nⁿ ≤ (n+1) · (n+1)ⁿ`. Il te faudra `Nat.pow_le_pow_left : a ≤ b → a ^ n ≤ b ^ n`.
-/
import Solutions.Recurrence.Definitions

/-!
# Qui grandit le plus vite ?

`n < 2ⁿ ≤ (n+1)! ≤ (n+1)ⁿ⁺¹`… les fonctions polynomiales, exponentielles et factorielles
n'ont pas la même vitesse. C'est le cœur de la **complexité** des algorithmes.

## À prouver
1. `lt_deux_pow (n : Nat) : n < 2 ^ n`
2. `deux_pow_le_fact (n : Nat) : 2 ^ n ≤ fact (n + 1)`
3. `fact_le_pow (n : Nat) : fact n ≤ n ^ n`
-/

namespace Parcours.Recurrence

theorem lt_deux_pow (n : Nat) : n < 2 ^ n := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

theorem deux_pow_le_fact (n : Nat) : 2 ^ n ≤ fact (n + 1) := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ, fact_succ, Nat.mul_comm]
    exact Nat.mul_le_mul (by omega) ih

theorem fact_le_pow (n : Nat) : fact n ≤ n ^ n := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    rw [fact_succ, Nat.pow_succ, Nat.mul_comm]
    apply Nat.mul_le_mul _ (Nat.le_refl _)
    exact Nat.le_trans ih (Nat.pow_le_pow_left (by omega) n)

end Parcours.Recurrence

#verifier
