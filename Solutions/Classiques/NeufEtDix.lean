/- @parcours
titre: Pourquoi la preuve par neuf marche
difficulte: 2
requiert: Classiques.Seize
indice: Récurrence ; `Nat.pow_succ`, `Nat.mul_mod`, `ih`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Pourquoi la preuve par neuf marche

## Se le représenter
`10 = 9 + 1` : toutes les puissances de 10 valent 1 modulo 9. Donc `abc = 100a + 10b + c ≡ a + b + c`.
C'est le secret de la preuve par neuf.

## À prouver
`dix_mod_neuf (n : Nat) : (10 ^ n) % 9 = 1`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem dix_mod_neuf (n : Nat) : (10 ^ n) % 9 = 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

end Parcours.Classiques

#verifier
