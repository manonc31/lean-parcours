/- @parcours
titre: Une chaîne de réécritures
difficulte: 1
requiert: Gymnase.RwDansHyp
indice: `rw [h1, h2, h3]`.
-/
import ParcoursOutils

/-!
# Une chaîne de réécritures

`rw [h1, h2, h3]` enchaîne plusieurs réécritures. Regarde l'infoview entre chaque étape (place le curseur après chaque virgule).

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem rw_chaine (a b c : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = 5) : a = 5 := by -- @exo
  rw [h1, h2, h3]

end Parcours.Gymnase

#verifier
