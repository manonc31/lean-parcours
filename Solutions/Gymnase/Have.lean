/- @parcours
titre: Étapes intermédiaires avec have
difficulte: 1
requiert: Gymnase.Apply
indice: `have hq : Q := hpq hp`.
-/
import ParcoursOutils

/-!
# Étapes intermédiaires avec have

`have hq : Q := hpq hp` ajoute un nouveau fait à tes hypothèses. Pratique pour découper une preuve.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem have_exemple (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by -- @exo
  have hq : Q := hpq hp
  have hr : R := hqr hq
  exact hr

end Parcours.Gymnase

#verifier
