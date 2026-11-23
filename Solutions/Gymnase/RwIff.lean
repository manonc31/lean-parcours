/- @parcours
titre: Réécrire avec une équivalence
difficulte: 2
requiert: Logique.Equivalence
indice: `rw [h]` puis `exact hq`.
-/
import ParcoursOutils

/-!
# Réécrire avec une équivalence

`rw` marche aussi avec `h : P ↔ Q` : il remplace la **proposition** `P` par `Q` dans le but.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem rw_iff (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by -- @exo
  rw [h]
  exact hq

end Parcours.Gymnase

#verifier
