/- @parcours
titre: Prouver une équivalence
difficulte: 2
requiert: Gymnase.Omega
indice: `constructor`, puis `intro h` dans chaque sens.
indice: Sens `→` : `rw [h]`. Sens `←` : `omega`.
-/
import Solutions.Naturels.Transfert

/-!
# Prouver une équivalence

Pour `P ↔ Q` : `constructor`, puis les deux sens.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem equivalence_exemple (n : Nat) : n = 0 ↔ n + 1 = 1 := by -- @exo
  constructor
  · intro h
    rw [h]
  · intro h
    omega

end Parcours.Gymnase

#verifier
