/- @parcours
titre: Échanger les hypothèses
difficulte: 1
requiert: Gymnase.Intro
indice: `intro h hq hp`, puis `exact h hp hq`.
-/
import ParcoursOutils

/-!
# Échanger les hypothèses

Une fonction de deux arguments peut prendre ses arguments dans l'autre ordre.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem echange (P Q R : Prop) : (P → Q → R) → (Q → P → R) := by -- @exo
  intro h hq hp
  exact h hp hq

end Parcours.Gymnase

#verifier
