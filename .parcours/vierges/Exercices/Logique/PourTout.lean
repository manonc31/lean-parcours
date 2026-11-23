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

---
*Exercice* `Logique.PourTout` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.PourTout` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {α : Type} {p q : α → Prop}

theorem pourtout_et : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  sorry

theorem pourtout_impl (h : ∀ x, p x → q x) (hp : ∀ x, p x) : ∀ x, q x := by
  sorry

theorem pourtout_ou (h : (∀ x, p x) ∨ (∀ x, q x)) : ∀ x, p x ∨ q x := by
  sorry

theorem pourtout_echange {r : α → α → Prop} : (∀ x y, r x y) ↔ (∀ y x, r x y) := by
  sorry

end Parcours.Logique

#verifier
