/- @parcours
titre: √3 est irrationnel
difficulte: 2
requiert: Arithmetique.TestPrimalite
indice: `racine_premier_irrationnelle` attend une preuve de `Premier 3`.
indice: `(estPremier_correct 3).mp (by decide)` en fournit une.
-/
import Solutions.Arithmetique.RacinePremier
import Solutions.Arithmetique.TestPrimalite

/-!
# √3 est irrationnel

## Se le représenter
Tu as prouvé que `√p` est irrationnel pour tout premier `p`, et tu as un test de primalité.
Assemble les deux !

## À prouver
`racine_trois : ¬∃ a b : Nat, 0 < b ∧ a * a = 3 * (b * b)`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

open Parcours.Arith

theorem racine_trois : ¬∃ a b : Nat, 0 < b ∧ a * a = 3 * (b * b) := by -- @exo
  exact racine_premier_irrationnelle ((estPremier_correct 3).mp (by decide))

end Parcours.Classiques

#verifier
