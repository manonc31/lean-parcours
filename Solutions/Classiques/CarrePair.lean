/- @parcours
titre: Un carré est pair ssi…
difficulte: 1
requiert: Olympiades.Parite
indice: Deux cas sur `n % 2` ; `simp [Nat.mul_mod, h]`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Un carré est pair ssi…

## Se le représenter
Si `n` est impair, `n × n` aussi (impair × impair = impair). C'est l'argument clé de l'irrationalité de √2.

## À prouver
`carre_pair (n : Nat) : (n * n) % 2 = 0 ↔ n % 2 = 0`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem carre_pair (n : Nat) : (n * n) % 2 = 0 ↔ n % 2 = 0 := by -- @exo
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.mul_mod, h]

end Parcours.Classiques

#verifier
