/- @parcours
titre: Le quantificateur « pour tout »
difficulte: 2
requiert: Logique.Et, Logique.Ou
indice: Pour prouver `∀ x, …`, commence par `intro x`.
indice: `h : ∀ x, p x ∧ q x` est une fonction : `h x : p x ∧ q x`, donc `(h x).1 : p x`.
indice: `fun x => …` construit directement une preuve de `∀ x, …`.
-/
import ParcoursOutils

/-!
# Le quantificateur universel (∀)

Une preuve de `∀ x, p x` est une **fonction** qui, à chaque `x`, associe une preuve de `p x`.

- **Construire** : `intro x` (soit `x` quelconque…), ou `fun x => …`.
- **Utiliser** `h : ∀ x, p x` : `h a : p a` pour n'importe quel `a`.

Ici `α` est un type quelconque et `p q : α → Prop` sont des propriétés des éléments de `α`.

## À prouver
1. `pourtout_et : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x)`
2. `pourtout_impl : (∀ x, p x → q x) → (∀ x, p x) → ∀ x, q x`
3. `pourtout_ou : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x`
4. `pourtout_echange : (∀ x y, r x y) ↔ (∀ y x, r x y)`

(La réciproque de 3 est fausse : pense à « tout entier est pair ou impair ».)
-/

namespace Parcours.Logique

variable {α : Type} {p q : α → Prop}

theorem pourtout_et : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by -- @exo
  constructor
  · intro h
    exact ⟨fun x => (h x).1, fun x => (h x).2⟩
  · rintro ⟨hp, hq⟩ x
    exact ⟨hp x, hq x⟩

theorem pourtout_impl (h : ∀ x, p x → q x) (hp : ∀ x, p x) : ∀ x, q x := by -- @exo
  intro x
  exact h x (hp x)

theorem pourtout_ou (h : (∀ x, p x) ∨ (∀ x, q x)) : ∀ x, p x ∨ q x := by -- @exo
  intro x
  rcases h with hp | hq
  · exact Or.inl (hp x)
  · exact Or.inr (hq x)

theorem pourtout_echange {r : α → α → Prop} : (∀ x y, r x y) ↔ (∀ y x, r x y) := by -- @exo
  exact ⟨fun h y x => h x y, fun h x y => h y x⟩

end Parcours.Logique

#verifier
