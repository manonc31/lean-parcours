import Exercices.Informatique.Expressions

/-!
# Le point fixe de Lawvere

> Si `f : A → (A → B)` est surjective, alors **toute** fonction `h : B → B` a un point fixe.

Ce théorème de William Lawvere (1969) unifie d'un coup : le théorème de Cantor, le paradoxe de
Russell, l'indécidabilité de l'arrêt, le théorème d'incomplétude de Gödel… C'est l'essence de
**tous** les arguments diagonaux.

## À prouver
1. `lawvere : (∀ g : A → B, ∃ a, f a = g) → ∀ h : B → B, ∃ b, h b = b`
2. `cantor_bool` : il n'y a pas de surjection `A → (A → Bool)` (car `not` n'a pas de point fixe).

## Ressources
- [Théorème du point fixe de Lawvere (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Lawvere%27s_fixed-point_theorem)

---
*Exercice* `Informatique.Lawvere` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Informatique.Lawvere` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

theorem lawvere {A B : Type} (f : A → A → B) (hf : ∀ g : A → B, ∃ a, f a = g) (h : B → B) :
    ∃ b, h b = b := by
  sorry

theorem cantor_bool {A : Type} (f : A → A → Bool) : ¬∀ g : A → Bool, ∃ a, f a = g := by
  sorry

end Parcours.Info

#verifier
