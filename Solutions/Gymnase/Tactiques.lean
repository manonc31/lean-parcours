/- @parcours
titre: Enchaîner les tactiques
difficulte: 2
requiert: Gymnase.Rcases
indice: `constructor <;> constructor <;> assumption` (`assumption` cherche une hypothèse qui convient).
-/
import ParcoursOutils

/-!
# Enchaîner les tactiques

`t1 <;> t2` applique `t2` à **tous** les buts créés par `t1`. Pratique quand plusieurs cas se prouvent de la même façon.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem enchainer (P Q : Prop) (hp : P) (hq : Q) : (P ∧ Q) ∧ (Q ∧ P) := by -- @exo
  constructor <;> constructor <;> assumption

end Parcours.Gymnase

#verifier
