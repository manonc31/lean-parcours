/- @parcours
titre: Réécrire à l'envers
difficulte: 1
requiert: Gymnase.RwSimple
indice: `rw [← h]`.
-/
import ParcoursOutils

/-!
# Réécrire à l'envers

Ici `h : 4 = y` : on veut remplacer `y` par `4`, c'est-à-dire réécrire de **droite à gauche** : `rw [← h]` (la flèche se tape `\l`).

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem rw_arriere (y : Nat) (h : 4 = y) : y + 1 = 5 := by -- @exo
  rw [← h]

end Parcours.Gymnase

#verifier
