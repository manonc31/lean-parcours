/- @parcours
titre: Raisonner sur les booléens
difficulte: 1
requiert: Gymnase.Decide
indice: `cases b <;> rfl`.
indice: Pour deux booléens : `cases a <;> cases b <;> rfl`.
-/
import ParcoursOutils

/-!
# Raisonner sur les booléens

Un booléen est `true` ou `false`. `cases b` examine les deux cas ; dans chacun, `rfl` calcule. Raccourci : `cases b <;> rfl` applique `rfl` à tous les cas.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem et_vrai (b : Bool) : (b && true) = b := by -- @exo
  cases b <;> rfl

theorem non_non (b : Bool) : (!(!b)) = b := by -- @exo
  cases b <;> rfl

theorem ou_comm_bool (a b : Bool) : (a || b) = (b || a) := by -- @exo
  cases a <;> cases b <;> rfl

end Parcours.Gymnase

#verifier
