/- @parcours
titre: Bijections et réciproques
difficulte: 3
indice: Sens `→` : `inverse_droite` donne un `g` avec `f (g y) = y`. Montre que c'est aussi un inverse à gauche avec l'injectivité : `f (g (f x)) = f x`.
indice: Sens `←` : tu as déjà `injective_of_inverse_gauche` et `surjective_of_inverse_droite`.
-/
import Solutions.Fonctions.Choix
import Solutions.Fonctions.Inverses

/-!
# Bijections et réciproques

Une fonction est bijective si et seulement si elle a une **réciproque** (un inverse des deux côtés).

## À prouver
`bijective_iff : Bijective f ↔ ∃ g : β → α, (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)`
-/

namespace Parcours.Fonctions

variable {α β : Type} {f : α → β}

theorem bijective_iff : Bijective f ↔ ∃ g : β → α, (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) := by -- @exo
  constructor
  · rintro ⟨hi, hs⟩
    obtain ⟨g, hg⟩ := inverse_droite hs
    exact ⟨g, fun x => hi _ _ (hg (f x)), hg⟩
  · rintro ⟨g, hgf, hfg⟩
    exact ⟨injective_of_inverse_gauche hgf, surjective_of_inverse_droite hfg⟩

end Parcours.Fonctions

#verifier
