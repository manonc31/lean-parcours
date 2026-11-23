import Exercices.Fonctions.Definitions

/-!
# Composer des injections et des surjections

## À prouver
1. `injective_comp` : la composée de deux injections est injective.
2. `surjective_comp` : la composée de deux surjections est surjective.
3. `bijective_comp` : la composée de deux bijections est bijective.

---
*Exercice* `Fonctions.Composition` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Fonctions.Composition` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

variable {α β γ : Type} {f : α → β} {g : β → γ}

theorem injective_comp (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  sorry

theorem surjective_comp (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  sorry

theorem bijective_comp (hf : Bijective f) (hg : Bijective g) : Bijective (g ∘ f) := by
  sorry

end Parcours.Fonctions

#verifier
