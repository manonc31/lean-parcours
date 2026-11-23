/- @parcours
titre: Les nombres de Fibonacci
difficulte: 3
indice: `fib_pos` : `fib (n+1) > 0` ; récurrence (attention, deux cas de base car `fib` regarde deux étapes en arrière : fais plutôt une récurrence sur `n` qui prouve la propriété pour `n+1` et `n+2` à la fois).
indice: `fib_lt_deux_pow` : prouve `fib n < 2 ^ n ∧ fib (n + 1) < 2 ^ (n + 1)` par récurrence (les deux à la fois !), puis prends la première partie.
indice: `fib_add` : récurrence sur `n` en généralisant `m` (`induction n generalizing m`). Le cas `succ` utilise `ih (m + 1)` et `fib_add_two`, puis `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# Les nombres de Fibonacci

`0, 1, 1, 2, 3, 5, 8, 13, 21, 34…` : chaque terme est la somme des deux précédents.
Pour les propriétés qui regardent deux termes en arrière, une astuce : prouver **deux
énoncés à la fois** (`P n ∧ P (n+1)`) par récurrence.

## À prouver
1. `fib_lt_deux_pow (n : Nat) : fib n < 2 ^ n`
2. `fib_add (m n : Nat) : fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n`

## Ressources
- [Suite de Fibonacci (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Fibonacci)
-/

namespace Parcours.Recurrence

theorem fib_lt_deux_pow (n : Nat) : fib n < 2 ^ n := by -- @exo
  have h : ∀ n, fib n < 2 ^ n ∧ fib (n + 1) < 2 ^ (n + 1) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [fib_add_two, Nat.pow_succ, Nat.pow_succ]
      have := ih.1
      have := ih.2
      rw [Nat.pow_succ] at this
      omega
  exact (h n).1

theorem fib_add (m n : Nat) : fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n := by -- @exo
  induction n generalizing m with
  | zero => simp [fib]
  | succ n ih =>
    have h := ih (m + 1)
    rw [show m + 1 + n + 1 = m + (n + 1) + 1 by omega] at h
    rw [h, fib_add_two, show fib (n + 1 + 1) = fib n + fib (n + 1) from fib_add_two n]
    grind

end Parcours.Recurrence

#verifier
