/- @parcours
titre: Construire un « et »
difficulte: 1
requiert: Logique.Et
indice: `constructor`, puis `· exact hq` et `· exact hp`.
-/
import ParcoursOutils

/-!
# Construire un « et »

`constructor` découpe le but `A ∧ B` en deux buts `A` et `B`. Traite-les avec `·` (tapé `\.`).

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem constructor_exemple (P Q : Prop) (hp : P) (hq : Q) : Q ∧ P := by -- @exo
  constructor
  · exact hq
  · exact hp

end Parcours.Gymnase

#verifier
