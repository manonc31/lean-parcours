/- @parcours
titre: n³ + 2n est divisible par 3
difficulte: 2
requiert: Olympiades.Parite
indice: Trois cas sur `n % 3`, puis `simp [Nat.add_mod, Nat.mul_mod, h]`.
-/
import Solutions.Arithmetique.Definitions

/-!
# n³ + 2n est divisible par 3

## Se le représenter
`n³ + 2n = n³ − n + 3n = (n−1)n(n+1) + 3n` : trois entiers consécutifs contiennent toujours un multiple
de 3. En Lean, on raisonne directement sur le reste de `n` modulo 3.

## À prouver
`divisible_trois (n : Nat) : (n * n * n + 2 * n) % 3 = 0`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem divisible_trois (n : Nat) : (n * n * n + 2 * n) % 3 = 0 := by -- @exo
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [Nat.add_mod, Nat.mul_mod, h]

end Parcours.Classiques

#verifier
