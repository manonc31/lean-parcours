/- @parcours
titre: Faire vérifier par la machine
difficulte: 1
requiert: Gymnase.Contradiction
indice: `decide` à chaque fois.
-/
import ParcoursOutils

/-!
# Faire vérifier par la machine

Pour un énoncé **sans variable** qui se vérifie par calcul (égalités, inégalités, `≠` sur des nombres…), `decide` fait le calcul et conclut.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem decide_ne : (2 : Nat) ≠ 3 := by -- @exo
  decide

theorem decide_reste : (17 : Nat) % 5 = 2 := by -- @exo
  decide

theorem decide_ou : (10 : Nat) < 3 ∨ 2 ≤ 2 := by -- @exo
  decide

end Parcours.Gymnase

#verifier
