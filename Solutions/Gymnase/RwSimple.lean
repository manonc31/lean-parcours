/- @parcours
titre: Remplacer une variable
difficulte: 1
requiert: Tutoriel.Reecrire
indice: `rw [h]` et c'est fini : après réécriture, le but `3 + 3 = 6` se calcule.
-/
import ParcoursOutils

/-!
# Remplacer une variable

`rw [h]` remplace `x` par `3` partout dans le but. Ensuite, `rw` essaie `rfl` tout seul.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem rw_simple (x : Nat) (h : x = 3) : x + x = 6 := by -- @exo
  rw [h]

end Parcours.Gymnase

#verifier
