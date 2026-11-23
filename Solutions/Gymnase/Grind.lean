/- @parcours
titre: La tactique grind
difficulte: 2
requiert: Naturels.Carre
indice: `grind`.
indice: Pour le second : `subst h` remplace `x` par `y + 1`, puis `grind`.
-/
import Solutions.Naturels.Carre
import Solutions.Logique.Bilan
import Solutions.Naturels.Transfert

/-!
# La tactique grind

Depuis l'identité remarquable, **`grind`** est débloqué. C'est un « couteau suisse » : il combine calcul algébrique (anneaux), arithmétique linéaire, et raisonnement sur les égalités.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem grind1 (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by -- @exo
  grind

theorem grind2 (x y : Int) (h : x = y + 1) : x * x - y * y = 2 * y + 1 := by -- @exo
  subst h
  grind

end Parcours.Gymnase

#verifier
