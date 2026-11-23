/- @parcours
titre: Décider sur un ensemble fini
difficulte: 1
requiert: Gymnase.Decide
indice: `decide`.
-/
import ParcoursOutils

/-!
# Décider sur un ensemble fini

`Fin n` est le type des entiers `< n`. Un énoncé `∀ x : Fin 4, …` n'a que 4 cas : `decide` les vérifie tous.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem fini1 : ∀ x : Fin 4, x.val * x.val < 10 := by -- @exo
  decide

theorem fini2 : (List.range 5).foldl (· + ·) 0 = 10 := by -- @exo
  decide

end Parcours.Gymnase

#verifier
