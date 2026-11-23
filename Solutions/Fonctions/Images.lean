/- @parcours
titre: Images et images réciproques
difficulte: 3
indice: `x ∈ f '' s` signifie `∃ a, a ∈ s ∧ f a = x` : pour le prouver, donne un témoin ; pour l'utiliser, `obtain ⟨a, ha, rfl⟩ := h` (le `rfl` remplace directement `x` par `f a`).
indice: `image_union` : dans le sens `→`, `obtain ⟨a, ha | ha, rfl⟩`.
indice: `image_inter_injective` : si `y = f a = f b` avec `a ∈ s` et `b ∈ t`, l'injectivité donne `a = b`.
-/
import Solutions.Fonctions.Ensembles

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
-/

namespace Parcours.Fonctions

variable {α β : Type} {f : α → β} {s s' : Ens α} {t₁ t₂ : Ens β}

theorem preimage_inter : f ⁻¹' (t₁ ∩ t₂) = f ⁻¹' t₁ ∩ f ⁻¹' t₂ := by -- @exo
  apply ext
  intro x
  exact Iff.rfl

theorem image_union : f '' (s ∪ s') = f '' s ∪ f '' s' := by -- @exo
  apply ext
  intro y
  constructor
  · rintro ⟨a, ha | ha, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩

theorem image_inter_subset : f '' (s ∩ s') ⊆ f '' s ∩ f '' s' := by -- @exo
  rintro y ⟨a, ⟨ha, ha'⟩, rfl⟩
  exact ⟨⟨a, ha, rfl⟩, ⟨a, ha', rfl⟩⟩

theorem image_inter_injective (hf : Injective f) : f '' s ∩ f '' s' ⊆ f '' (s ∩ s') := by -- @exo
  rintro y ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
  have : b = a := hf b a hab
  rw [this] at hb
  exact ⟨a, ⟨ha, hb⟩, rfl⟩

theorem subset_preimage_image : s ⊆ f ⁻¹' (f '' s) := by -- @exo
  intro x hx
  exact ⟨x, hx, rfl⟩

end Parcours.Fonctions

#verifier
