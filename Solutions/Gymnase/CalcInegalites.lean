/- @parcours
titre: calc avec des inégalités
difficulte: 2
requiert: Gymnase.Calc
indice: `calc a + 1 ≤ b + 1 := by omega` puis `_ < c + 1 := by omega`.
indice: Ou directement `omega` !
-/
import Solutions.Naturels.Transfert

/-!
# calc avec des inégalités

`calc` marche aussi avec `≤` et `<` : chaque étape peut être `=`, `≤` ou `<`, et Lean combine.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem calc_ineg (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a + 1 < c + 1 := by -- @exo
  calc a + 1 ≤ b + 1 := by omega
    _ < c + 1 := by omega

end Parcours.Gymnase

#verifier
