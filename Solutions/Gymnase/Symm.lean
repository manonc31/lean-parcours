/- @parcours
titre: Retourner une égalité
difficulte: 1
requiert: Gymnase.RwSimple
indice: `exact h.symm`.
indice: Pour le second : `exact h1.trans h2` (ou `rw [h1, h2]`).
-/
import ParcoursOutils

/-!
# Retourner une égalité

Si `h : 3 = x`, alors `h.symm : x = 3`. Le point permet d'appeler une fonction associée au type de `h` (ici `Eq.symm`) : c'est la **notation pointée**.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem symm_exemple (x : Nat) (h : 3 = x) : x = 3 := by -- @exo
  exact h.symm

theorem trans_exemple (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by -- @exo
  exact h1.trans h2

end Parcours.Gymnase

#verifier
