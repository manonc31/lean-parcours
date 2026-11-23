/- @parcours
titre: Le « et »
difficulte: 1
requiert: Logique.Implication
indice: Pour prouver `P ∧ Q`, utilise `constructor` (deux buts : `P` puis `Q`), ou directement `exact ⟨hp, hq⟩`.
indice: Pour utiliser `h : P ∧ Q` : `h.1 : P` et `h.2 : Q`, ou `obtain ⟨hp, hq⟩ := h`.
indice: Les chevrons `⟨ ⟩` se tapent `\<` et `\>`.
-/
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
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem et_intro (hp : P) (hq : Q) : P ∧ Q := by -- @exo
  exact ⟨hp, hq⟩

theorem et_gauche (h : P ∧ Q) : P := by -- @exo
  exact h.1

theorem et_comm (h : P ∧ Q) : Q ∧ P := by -- @exo
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

theorem et_assoc (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) := by -- @exo
  obtain ⟨⟨hp, hq⟩, hr⟩ := h
  exact ⟨hp, hq, hr⟩

end Parcours.Logique

#verifier
