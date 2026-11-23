/- @parcours
titre: Appliquer une fonction aux deux côtés
difficulte: 1
requiert: Gymnase.Symm
indice: `exact congrArg (fun x => x * 2) h`, ou plus simplement `rw [h]`.
-/
import ParcoursOutils

/-!
# Appliquer une fonction aux deux côtés

Si `a = b`, alors `f a = f b` : c'est `congrArg f h`. Ici la fonction est `fun x => x * 2`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem congr_exemple (a b : Nat) (h : a = b) : a * 2 = b * 2 := by -- @exo
  exact congrArg (fun x => x * 2) h

end Parcours.Gymnase

#verifier
