/- @parcours
titre: Utiliser un « pour tout »
difficulte: 1
requiert: Gymnase.Have
indice: `exact h 5`.
indice: Pour le second : `intro n` puis `rfl`.
-/
import ParcoursOutils

/-!
# Utiliser un « pour tout »

`h : ∀ n, P n` s'applique à n'importe quel `n` : `h 5 : P 5`. Variante : `specialize h 5` remplace `h` par `h 5`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem pour_tout_exemple (P : Nat → Prop) (h : ∀ n, P n) : P 5 := by -- @exo
  exact h 5

theorem pour_tout_intro : ∀ n : Nat, n = n := by -- @exo
  intro n
  rfl

end Parcours.Gymnase

#verifier
