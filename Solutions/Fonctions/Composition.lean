/- @parcours
titre: Composer des injections et des surjections
difficulte: 2
indice: Déplie la définition : `intro a b h` pour `Injective (g ∘ f)`. Le `h` est `(g ∘ f) a = (g ∘ f) b`, c'est-à-dire `g (f a) = g (f b)` par définition.
indice: `exact hf a b (hg (f a) (f b) h)`.
indice: Surjectivité : `intro z`, `obtain ⟨y, hy⟩ := hg z`, `obtain ⟨x, hx⟩ := hf y`, puis `exact ⟨x, by show g (f x) = z; rw [hx, hy]⟩`.
-/
import Solutions.Fonctions.Definitions

/-!
# Composer des injections et des surjections

## À prouver
1. `injective_comp` : la composée de deux injections est injective.
2. `surjective_comp` : la composée de deux surjections est surjective.
3. `bijective_comp` : la composée de deux bijections est bijective.
-/

namespace Parcours.Fonctions

variable {α β γ : Type} {f : α → β} {g : β → γ}

theorem injective_comp (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by -- @exo
  intro a b h
  exact hf a b (hg (f a) (f b) h)

theorem surjective_comp (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by -- @exo
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  exact ⟨x, by show g (f x) = z; rw [hx, hy]⟩

theorem bijective_comp (hf : Bijective f) (hg : Bijective g) : Bijective (g ∘ f) := by -- @exo
  exact ⟨injective_comp hf.1 hg.1, surjective_comp hf.2 hg.2⟩

end Parcours.Fonctions

#verifier
