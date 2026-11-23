/- @parcours
titre: Image par une composée
difficulte: 2
requiert: Fonctions.Images
indice: `apply ext`, puis deux sens. Utilise `rintro ⟨x, hx, rfl⟩` pour déstructurer une appartenance à une image.
-/
import Solutions.Fonctions.Definitions

/-!
# Image par une composée

L'image d'un ensemble par `g ∘ f` est l'image par `g` de l'image par `f`.

## À prouver
`image_comp : (g ∘ f) '' s = g '' (f '' s)`
-/

namespace Parcours.Fonctions

theorem image_comp {α β γ : Type} (f : α → β) (g : β → γ) (s : Ens α) :
    (g ∘ f) '' s = g '' (f '' s) := by -- @exo
  apply ext
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

end Parcours.Fonctions

#verifier
