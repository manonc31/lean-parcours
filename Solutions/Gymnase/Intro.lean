/- @parcours
titre: Introduire des hypothèses
difficulte: 1
requiert: Tutoriel.Hypotheses
indice: `intro hp hq` puis `exact hp`.
-/
import ParcoursOutils

/-!
# Introduire des hypothèses

Pour prouver `P → Q → P`, `intro hp hq` introduit les deux hypothèses ; il reste à prouver `P`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem intro_exemple (P Q : Prop) : P → Q → P := by -- @exo
  intro hp _
  exact hp

end Parcours.Gymnase

#verifier
