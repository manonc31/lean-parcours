/- @parcours
titre: Choisir un côté
difficulte: 1
requiert: Logique.Ou
indice: `right`, `left`, `exact hq`.
-/
import ParcoursOutils

/-!
# Choisir un côté

Pour prouver `P ∨ (Q ∨ R)` à partir de `Q` : `right` puis `left`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem gauche_droite (P Q R : Prop) (hq : Q) : P ∨ Q ∨ R := by -- @exo
  right
  left
  exact hq

end Parcours.Gymnase

#verifier
