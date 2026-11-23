/- @parcours
titre: Plusieurs quantificateurs
difficulte: 1
requiert: Gymnase.PourTout
indice: `intro a b h` puis `exact h.symm`.
-/
import ParcoursOutils

/-!
# Plusieurs quantificateurs

`intro a b h` introduit d'un coup tous les `∀` et les hypothèses.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem imbriques : ∀ a b : Nat, a = b → b = a := by -- @exo
  intro a b h
  exact h.symm

end Parcours.Gymnase

#verifier
