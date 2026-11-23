/- @parcours
titre: Le point fixe de Lawvere
difficulte: 3
indice: Applique la surjectivité à la fonction diagonale « tordue » `g x := h (f x x)`. Tu obtiens `a` avec `f a = g`.
indice: Alors `f a a = g a = h (f a a)` : `f a a` est un point fixe de `h` ! (`congrFun ha a`).
indice: `cantor_bool` : la négation booléenne `not` n'a pas de point fixe (`cases b` puis `simp at hb`).
-/
import Solutions.Informatique.Expressions

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
-/

namespace Parcours.Info

theorem lawvere {A B : Type} (f : A → A → B) (hf : ∀ g : A → B, ∃ a, f a = g) (h : B → B) :
    ∃ b, h b = b := by -- @exo
  obtain ⟨a, ha⟩ := hf (fun x => h (f x x))
  exact ⟨f a a, (congrFun ha a).symm⟩

theorem cantor_bool {A : Type} (f : A → A → Bool) : ¬∀ g : A → Bool, ∃ a, f a = g := by -- @exo
  intro hf
  obtain ⟨b, hb⟩ := lawvere f hf not
  cases b <;> simp at hb

end Parcours.Info

#verifier
