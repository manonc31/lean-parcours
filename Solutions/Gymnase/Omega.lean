/- @parcours
titre: La tactique omega
difficulte: 1
requiert: Naturels.Transfert
indice: `omega`.
-/
import Solutions.Naturels.Transfert

/-!
# La tactique omega

Depuis le Pont des entiers, la tactique **`omega`** est débloquée : elle résout toute seule les problèmes d'arithmétique **linéaire** (+, −, ≤, <, multiplication par une constante) sur `Nat` et `Int`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem omega1 (a b : Nat) (h : a < b) : a + 1 ≤ b := by -- @exo
  omega

theorem omega2 (x y : Nat) (h1 : x + y = 10) (h2 : x = y + 2) : x = 6 := by -- @exo
  omega

end Parcours.Gymnase

#verifier
