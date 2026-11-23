/- @parcours
titre: Trois chaussettes
difficulte: 1
requiert: Combinatoire.Tiroirs
indice: `omega` sait raisonner par cas tout seul.
-/
import Solutions.Arithmetique.Definitions

/-!
# Trois chaussettes

## Se le représenter
Dans un tiroir de chaussettes noires et blanches, il suffit d'en prendre **trois** pour avoir une paire
de la même couleur. Version nombres : parmi trois entiers, deux ont la même parité.

## À prouver
`trois_chaussettes (a b c : Nat) : a % 2 = b % 2 ∨ b % 2 = c % 2 ∨ a % 2 = c % 2`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem trois_chaussettes (a b c : Nat) : a % 2 = b % 2 ∨ b % 2 = c % 2 ∨ a % 2 = c % 2 := by -- @exo
  omega

end Parcours.Classiques

#verifier
