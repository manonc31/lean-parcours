import Exercices.Fonctions.Ensembles

/-!
# Images et images réciproques

- `f '' s` : l'ensemble des `f x` pour `x ∈ s`.
- `f ⁻¹' t` : l'ensemble des `x` tels que `f x ∈ t`.

L'image réciproque se comporte parfaitement avec toutes les opérations ; l'image… presque.

## À prouver
1. `preimage_inter : f ⁻¹' (t₁ ∩ t₂) = f ⁻¹' t₁ ∩ f ⁻¹' t₂`
2. `image_union : f '' (s ∪ s') = f '' s ∪ f '' s'`
3. `image_inter_subset : f '' (s ∩ s') ⊆ f '' s ∩ f '' s'`
4. `image_inter_injective : Injective f → f '' s ∩ f '' s' ⊆ f '' (s ∩ s')`
5. `subset_preimage_image : s ⊆ f ⁻¹' (f '' s)`

---
*Exercice* `Fonctions.Images` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Fonctions.Images` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

variable {α β : Type} {f : α → β} {s s' : Ens α} {t₁ t₂ : Ens β}

theorem preimage_inter : f ⁻¹' (t₁ ∩ t₂) = f ⁻¹' t₁ ∩ f ⁻¹' t₂ := by
  sorry

theorem image_union : f '' (s ∪ s') = f '' s ∪ f '' s' := by
  sorry

theorem image_inter_subset : f '' (s ∩ s') ⊆ f '' s ∩ f '' s' := by
  sorry

theorem image_inter_injective (hf : Injective f) : f '' s ∩ f '' s' ⊆ f '' (s ∩ s') := by
  sorry

theorem subset_preimage_image : s ⊆ f ⁻¹' (f '' s) := by
  sorry

end Parcours.Fonctions

#verifier
