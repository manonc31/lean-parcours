/- @parcours
titre: Un Fibonacci sur trois est pair
difficulte: 2
requiert: Classiques.FibSomme
indice: `motif` : récurrence sur `k`, avec `fib_add_two` pour écrire les trois termes suivants.
indice: `fib_pair` : écris `n = 3q`, `3q + 1` ou `3q + 2`.
-/
import Solutions.Recurrence.Definitions

/-!
# Un Fibonacci sur trois est pair

## Se le représenter
`0, 1, 1, 2, 3, 5, 8, 13, 21, 34…` : pair, impair, impair, pair, impair, impair… Le motif se
répète car impair + impair = pair, impair + pair = impair, pair + impair = impair.

## À prouver
1. `motif : fib (3k) % 2 = 0 ∧ fib (3k + 1) % 2 = 1 ∧ fib (3k + 2) % 2 = 1`
2. `fib_pair : fib n % 2 = 0 ↔ n % 3 = 0`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem motif (k : Nat) : fib (3 * k) % 2 = 0 ∧ fib (3 * k + 1) % 2 = 1 ∧ fib (3 * k + 2) % 2 = 1 := by -- @exo
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e0 : fib (3 * (k + 1)) = fib (3 * k + 1) + fib (3 * k + 2) := by
      rw [show 3 * (k + 1) = (3 * k + 1) + 2 by omega, fib_add_two]
    have e1 : fib (3 * (k + 1) + 1) = fib (3 * k + 2) + fib (3 * (k + 1)) := by
      rw [show 3 * (k + 1) + 1 = (3 * k + 2) + 2 by omega, fib_add_two]
      rfl
    have e2 : fib (3 * (k + 1) + 2) = fib (3 * (k + 1)) + fib (3 * (k + 1) + 1) := fib_add_two _
    omega

theorem fib_pair (n : Nat) : fib n % 2 = 0 ↔ n % 3 = 0 := by -- @exo
  obtain ⟨h0, h1, h2⟩ := motif (n / 3)
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h
  · rw [show n = 3 * (n / 3) by omega]
    omega
  · rw [show n = 3 * (n / 3) + 1 by omega]
    omega
  · rw [show n = 3 * (n / 3) + 2 by omega]
    omega

end Parcours.Classiques

#verifier
