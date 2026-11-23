import ParcoursOutils

/-!
# Le « et » (∧)

Une preuve de `P ∧ Q` est un **couple** : une preuve de `P` et une preuve de `Q`.

- **Construire** : `exact ⟨hp, hq⟩`, ou `constructor` (qui crée deux buts).
- **Utiliser** `h : P ∧ Q` : `h.1 : P`, `h.2 : Q`, ou `obtain ⟨hp, hq⟩ := h` qui découpe `h`.

Le symbole `∧` se tape `\and`. Quand il y a plusieurs buts, `·` (tapé `\.`) permet de les traiter un par un.

## À prouver
1. `et_intro` : de `P` et `Q`, déduire `P ∧ Q`.
2. `et_gauche` : de `P ∧ Q`, déduire `P`.
3. `et_comm` : de `P ∧ Q`, déduire `Q ∧ P`.
4. `et_assoc` : de `(P ∧ Q) ∧ R`, déduire `P ∧ (Q ∧ R)`.

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Propositions and Proofs*, section *Conjunction*.

---
*Exercice* `Logique.Et` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Logique.Et` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem et_intro (hp : P) (hq : Q) : P ∧ Q := by
  sorry

theorem et_gauche (h : P ∧ Q) : P := by
  sorry

theorem et_comm (h : P ∧ Q) : Q ∧ P := by
  sorry

theorem et_assoc (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) := by
  sorry

end Parcours.Logique

#verifier
