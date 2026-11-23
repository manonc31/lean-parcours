/- @parcours
titre: La moyenne est entre les deux
difficulte: 1
requiert: Gymnase.Omega
indice: `omega` connaît `/ 2`, `max` et `min`.
-/
import Solutions.Recurrence.Definitions

/-!
# La moyenne est entre les deux

## Se le représenter
La moyenne de deux nombres est entre les deux (ici avec la division entière).

## À prouver
`moyenne : a ≤ b → a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b`, et `max_min : max a b + min a b = a + b`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem moyenne (a b : Nat) (h : a ≤ b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by -- @exo
  omega

theorem max_min (a b : Nat) : max a b + min a b = a + b := by -- @exo
  omega

end Parcours.Classiques

#verifier
