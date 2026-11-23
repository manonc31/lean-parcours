/- @parcours
titre: by_cases : vrai ou faux ?
difficulte: 2
requiert: Logique.Classique
indice: `by_cases h : P`.
-/
import ParcoursOutils

/-!
# by_cases : vrai ou faux ?

`by_cases h : P` crée deux cas : un avec `h : P`, l'autre avec `h : ¬P`. (Logique classique.)

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem par_cas (P Q : Prop) (h1 : P → Q) (h2 : ¬P → Q) : Q := by -- @exo
  by_cases h : P
  · exact h1 h
  · exact h2 h

end Parcours.Gymnase

#verifier
