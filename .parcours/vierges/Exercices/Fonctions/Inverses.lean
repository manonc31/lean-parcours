import Exercices.Fonctions.Definitions

/-!
# Inverses à gauche et à droite

Si `g ∘ f = id` (`g` est un inverse **à gauche** de `f`), alors `f` est injective.
Si `f ∘ g = id` (`g` est un inverse **à droite** de `f`), alors `f` est surjective.

## À prouver
1. `injective_of_inverse_gauche : (∀ x, g (f x) = x) → Injective f`
2. `surjective_of_inverse_droite : (∀ y, f (g y) = y) → Surjective f`
3. `injective_of_comp : Injective (g ∘ f) → Injective f`
4. `surjective_of_comp : Surjective (g ∘ f) → Surjective g`

---
*Exercice* `Fonctions.Inverses` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Fonctions.Inverses` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

variable {α β γ : Type}

theorem injective_of_inverse_gauche {f : α → β} {g : β → α} (h : ∀ x, g (f x) = x) :
    Injective f := by
  sorry

theorem surjective_of_inverse_droite {f : α → β} {g : β → α} (h : ∀ y, f (g y) = y) :
    Surjective f := by
  sorry

theorem injective_of_comp {f : α → β} {g : β → γ} (h : Injective (g ∘ f)) : Injective f := by
  sorry

theorem surjective_of_comp {f : α → β} {g : β → γ} (h : Surjective (g ∘ f)) : Surjective g := by
  sorry

end Parcours.Fonctions

#verifier
