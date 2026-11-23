/- @parcours
titre: Une somme télescopique
difficulte: 2
requiert: Recurrence.Impairs
indice: Récurrence. Dans le cas `succ`, il faut savoir que `n² ≤ (n+1)²` pour que la soustraction se passe bien (`Nat.pow_le_pow_left`).
indice: Puis `omega`.
-/
import Solutions.Recurrence.Definitions

/-!
# Une somme télescopique

## Se le représenter
`(1² − 0²) + (2² − 1²) + (3² − 2²) + ⋯` : chaque terme annule une partie du précédent, comme un
télescope qu'on replie. Il ne reste que le dernier carré.

## À prouver
`telescopique (n : Nat) : somme (fun i => (i + 1) ^ 2 - i ^ 2) n = n ^ 2`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem telescopique (n : Nat) : somme (fun i => (i + 1) ^ 2 - i ^ 2) n = n ^ 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, ih]
    have h : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega

end Parcours.Classiques

#verifier
