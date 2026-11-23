/- @parcours
titre: Les fonctions anonymes
difficulte: 1
requiert: Gymnase.Calcul
indice: `rfl` dans les deux cas : Lean simplifie `(fun x => …) a` tout seul (β-réduction).
-/
import ParcoursOutils

/-!
# Les fonctions anonymes

`fun x => x + 1` est la fonction qui à `x` associe `x + 1` (on peut aussi écrire `(· + 1)`). L'appliquer, c'est **remplacer** `x` : Lean le fait par calcul.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem anonyme : (fun x : Nat => x + 1) 2 = 3 := by -- @exo
  rfl

theorem eta (f : Nat → Nat) : (fun x => f x) = f := by -- @exo
  rfl

end Parcours.Gymnase

#verifier
