/- @parcours
titre: Repérer une contradiction
difficulte: 1
requiert: Gymnase.Exfalso
indice: `contradiction` dans les deux cas.
-/
import ParcoursOutils

/-!
# Repérer une contradiction

Avec `hp : P` et `hnp : ¬P`, la tactique `contradiction` conclut toute seule. Elle repère aussi les égalités impossibles entre constructeurs, comme `0 = n + 1`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem contradiction_exemple (P Q : Prop) (hp : P) (hnp : ¬P) : Q := by -- @exo
  contradiction

theorem pas_de_predecesseur (n : Nat) (h : n + 1 = 0) : False := by -- @exo
  contradiction

end Parcours.Gymnase

#verifier
