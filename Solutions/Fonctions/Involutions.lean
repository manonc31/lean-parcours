/- @parcours
titre: Les involutions
difficulte: 2
requiert: Fonctions.Inverses
indice: `f` est son propre inverse à gauche ET à droite : tu as déjà les deux théorèmes qu'il faut (exercice « Inverses »).
-/
import Solutions.Fonctions.Inverses

/-!
# Les involutions

Une **involution** est une fonction qui est sa propre réciproque : `f (f x) = x` (comme la négation,
le passage à l'opposé, ou le miroir d'une liste). Une involution est toujours bijective.

## À prouver
`involution_bijective (h : ∀ x, f (f x) = x) : Bijective f`
-/

namespace Parcours.Fonctions

theorem involution_bijective {α : Type} {f : α → α} (h : ∀ x, f (f x) = x) : Bijective f := by -- @exo
  exact ⟨injective_of_inverse_gauche h, surjective_of_inverse_droite h⟩

end Parcours.Fonctions

#verifier
