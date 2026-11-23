/- @parcours
titre: Les limites d'omega
difficulte: 2
requiert: Gymnase.Omega
indice: `have h : 2 * 3 ≤ a * b := Nat.mul_le_mul ha hb`, puis `omega`.
-/
import Solutions.Naturels.Transfert

/-!
# Les limites d'omega

`omega` ne comprend pas la multiplication de deux **variables** (`a * b`) : il la traite comme une boîte noire. Ici, il faut d'abord établir un fait sur `a * b` avec un lemme (`Nat.mul_le_mul`), puis laisser `omega` finir.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem omega_limite (a b : Nat) (ha : 2 ≤ a) (hb : 3 ≤ b) : 6 ≤ a * b + 0 := by -- @exo
  have h : 2 * 3 ≤ a * b := Nat.mul_le_mul ha hb
  omega

end Parcours.Gymnase

#verifier
