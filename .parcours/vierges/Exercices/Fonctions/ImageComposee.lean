import Exercices.Fonctions.Definitions

/-!
# Image par une composée

L'image d'un ensemble par `g ∘ f` est l'image par `g` de l'image par `f`.

## À prouver
`image_comp : (g ∘ f) '' s = g '' (f '' s)`

---
*Exercice* `Fonctions.ImageComposee` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Fonctions.ImageComposee` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

theorem image_comp {α β γ : Type} (f : α → β) (g : β → γ) (s : Ens α) :
    (g ∘ f) '' s = g '' (f '' s) := by
  sorry

end Parcours.Fonctions

#verifier
