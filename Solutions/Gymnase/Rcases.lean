/- @parcours
titre: Raisonner par cas
difficulte: 1
requiert: Gymnase.Gauche
indice: `rcases h with hp | hq` puis deux `exact`.
-/
import ParcoursOutils

/-!
# Raisonner par cas

`rcases h with hp | hq` crée deux buts : un où `P` est vrai, un où `Q` est vrai.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem rcases_exemple (P Q R : Prop) (h : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by -- @exo
  rcases h with hp | hq
  · exact hpr hp
  · exact hqr hq

end Parcours.Gymnase

#verifier
