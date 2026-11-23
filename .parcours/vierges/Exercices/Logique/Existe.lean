import ParcoursOutils

/-!
# Le quantificateur existentiel (∃)

Une preuve de `∃ x, p x` est un **couple** : un témoin `a` et une preuve de `p a`.

- **Construire** : `exact ⟨a, ha⟩` (ou `refine ⟨a, ?_⟩` pour prouver `p a` ensuite).
- **Utiliser** `h : ∃ x, p x` : `obtain ⟨x, hx⟩ := h` (« soit `x` tel que… »).

## À prouver
1. `existe_ou : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x)`
2. `existe_et : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ (∃ x, q x)`
3. `existe_pourtout : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y`
4. `reciproque_fausse` : la réciproque de 3 est **fausse** en général !
   On le montre avec `α := Bool` et `r x y := (x = y)` : chaque `y` est égal à quelqu'un,
   mais personne n'est égal à tout le monde.

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Quantifiers and Equality*.

---
*Exercice* `Logique.Existe` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Logique.Existe` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {α : Type} {p q : α → Prop}

theorem existe_ou : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  sorry

theorem existe_et (h : ∃ x, p x ∧ q x) : (∃ x, p x) ∧ (∃ x, q x) := by
  sorry

theorem existe_pourtout {r : α → α → Prop} (h : ∃ x, ∀ y, r x y) : ∀ y, ∃ x, r x y := by
  sorry

theorem reciproque_fausse :
    ¬(∀ r : Bool → Bool → Prop, (∀ y, ∃ x, r x y) → ∃ x, ∀ y, r x y) := by
  sorry

end Parcours.Logique

#verifier
