/- @parcours
titre: Lean sait calculer
difficulte: 1
requiert: Tutoriel.Bienvenue
indice: `rfl` dans les deux cas.
-/
import ParcoursOutils

/-!
# Lean sait calculer

Quand les deux côtés d'une égalité se **calculent** en la même valeur, `rfl` suffit : Lean évalue `2 + 3` tout seul. (On peut aussi demander à Lean de calculer avec `#eval 2 + 3` : essaie !)

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem calcul : (2 : Nat) + 3 = 5 := by -- @exo
  rfl

theorem calcul_bis : (7 : Nat) * 6 = 42 := by -- @exo
  rfl

end Parcours.Gymnase

#verifier
