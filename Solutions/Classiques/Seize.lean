/- @parcours
titre: Les puissances de 16 et le chiffre 5
difficulte: 2
requiert: Olympiades.Sept
indice: Récurrence ; `Nat.pow_succ`, `Nat.mul_mod`, `ih`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Les puissances de 16 et le chiffre 5

## Se le représenter
`16 = 15 + 1`, donc toutes les puissances de 16 valent 1 modulo 5 (et se terminent par 6 en base 10 !).

## À prouver
`seize (n : Nat) : (16 ^ n) % 5 = 1`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem seize (n : Nat) : (16 ^ n) % 5 = 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

end Parcours.Classiques

#verifier
