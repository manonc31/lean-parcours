/- @parcours
titre: Les involutions des booléens
difficulte: 2
requiert: Fonctions.Involutions
indice: Quatre cas selon les valeurs de `f true` et `f false` (`cases ht : f true`).
indice: Pour conclure `f = id`, `funext b` puis `cases b`.
-/
import Solutions.Logique.Bilan

/-!
# Les involutions des booléens

Une fonction `f` est une **involution** si `f (f x) = x` pour tout `x` (la refaire annule son
effet, comme retourner une crêpe). Sur les booléens, il n'y en a que deux : l'identité et la
négation.

## À prouver
`involutions : (∀ b, f (f b) = b) → f = id ∨ f = not`
-/

namespace Parcours.Fonctions

theorem involutions (f : Bool → Bool) (h : ∀ b, f (f b) = b) : f = id ∨ f = not := by -- @exo
  cases ht : f true <;> cases hf : f false
  · have := h true
    rw [ht, hf] at this
    exact absurd this (by decide)
  · right
    funext b
    cases b <;> assumption
  · left
    funext b
    cases b <;> assumption
  · have := h false
    rw [hf, ht] at this
    exact absurd this (by decide)

end Parcours.Fonctions

#verifier
