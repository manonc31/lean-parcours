/- @parcours
titre: Une égalité absurde
difficulte: 1
requiert: Gymnase.Contradiction
indice: `exact absurd h (by decide)`.
-/
import ParcoursOutils

/-!
# Une égalité absurde

`2 = 3` est faux, et `decide` le sait : `(by decide : (2 : Nat) ≠ 3)`. Avec `absurd h preuve_de_non_h`, on conclut n'importe quoi.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem absurde (h : (2 : Nat) = 3) : False := by -- @exo
  exact absurd h (by decide)

end Parcours.Gymnase

#verifier
