/- @parcours
titre: Inverses à gauche et à droite
difficulte: 2
indice: `injective_of_inverse_gauche` : de `f a = f b`, applique `g` des deux côtés (`congrArg g h`), puis utilise `h`.
indice: Pour `injective_of_comp`, si `f a = f b` alors `g (f a) = g (f b)`.
indice: Pour `surjective_of_comp`, un antécédent de `z` par `g ∘ f` est `x` ; alors `f x` est un antécédent par `g`.
-/
import Solutions.Fonctions.Definitions

/-!
# Inverses à gauche et à droite

Si `g ∘ f = id` (`g` est un inverse **à gauche** de `f`), alors `f` est injective.
Si `f ∘ g = id` (`g` est un inverse **à droite** de `f`), alors `f` est surjective.

## À prouver
1. `injective_of_inverse_gauche : (∀ x, g (f x) = x) → Injective f`
2. `surjective_of_inverse_droite : (∀ y, f (g y) = y) → Surjective f`
3. `injective_of_comp : Injective (g ∘ f) → Injective f`
4. `surjective_of_comp : Surjective (g ∘ f) → Surjective g`
-/

namespace Parcours.Fonctions

variable {α β γ : Type}

theorem injective_of_inverse_gauche {f : α → β} {g : β → α} (h : ∀ x, g (f x) = x) :
    Injective f := by -- @exo
  intro a b hab
  rw [← h a, ← h b, hab]

theorem surjective_of_inverse_droite {f : α → β} {g : β → α} (h : ∀ y, f (g y) = y) :
    Surjective f := by -- @exo
  intro y
  exact ⟨g y, h y⟩

theorem injective_of_comp {f : α → β} {g : β → γ} (h : Injective (g ∘ f)) : Injective f := by -- @exo
  intro a b hab
  apply h a b
  show g (f a) = g (f b)
  rw [hab]

theorem surjective_of_comp {f : α → β} {g : β → γ} (h : Surjective (g ∘ f)) : Surjective g := by -- @exo
  intro z
  obtain ⟨x, hx⟩ := h z
  exact ⟨f x, hx⟩

end Parcours.Fonctions

#verifier
