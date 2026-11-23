/- @parcours
titre: Du faux, on déduit n'importe quoi
difficulte: 1
requiert: Logique.Negation
indice: `exfalso` puis `exact h`.
-/
import ParcoursOutils

/-!
# Du faux, on déduit n'importe quoi

Si tu as `h : False`, `exfalso` remplace le but par `False`, puis `exact h`. (Ou directement `exact h.elim`.)

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem exfalso_exemple (h : False) : (2 : Nat) + 2 = 5 := by -- @exo
  exfalso
  exact h

end Parcours.Gymnase

#verifier
