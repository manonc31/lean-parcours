/- @parcours
titre: Réécrire dans une hypothèse
difficulte: 1
requiert: Gymnase.RwArriere
indice: `rw [h1] at h2`, puis `exact h2`.
-/
import ParcoursOutils

/-!
# Réécrire dans une hypothèse

`rw [h1] at h2` réécrit **dans l'hypothèse** `h2` au lieu du but. Puis `exact h2`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem rw_dans_hyp (a b : Nat) (h1 : a = b) (h2 : a + 1 = 7) : b + 1 = 7 := by -- @exo
  rw [h1] at h2
  exact h2

end Parcours.Gymnase

#verifier
