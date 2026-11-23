/- @parcours
titre: Raisonner à rebours avec apply
difficulte: 1
requiert: Gymnase.Intro
indice: `apply hqr`, `apply hpq`, `exact hp`.
-/
import ParcoursOutils

/-!
# Raisonner à rebours avec apply

`apply hqr` : « pour prouver `R`, il suffit de prouver `Q` ». Le but devient `Q`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem apply_exemple (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by -- @exo
  apply hqr
  apply hpq
  exact hp

end Parcours.Gymnase

#verifier
