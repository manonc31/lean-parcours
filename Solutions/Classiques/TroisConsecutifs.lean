/- @parcours
titre: Trois entiers consécutifs
difficulte: 2
requiert: Classiques.Divisible3
indice: Six cas sur `n % 6`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Trois entiers consécutifs

## Se le représenter
Parmi trois entiers consécutifs, il y a un multiple de 2 et un multiple de 3 : leur produit est
divisible par 6.

## À prouver
`trois_consecutifs (n : Nat) : (n * (n + 1) * (n + 2)) % 6 = 0`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem trois_consecutifs (n : Nat) : (n * (n + 1) * (n + 2)) % 6 = 0 := by -- @exo
  have : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases this with h | h | h | h | h | h <;> simp [Nat.add_mod, Nat.mul_mod, h]

end Parcours.Classiques

#verifier
