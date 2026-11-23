import ParcoursOutils

/-!
# L'implication

En Lean, une preuve de `P → Q` est une **fonction** qui transforme une preuve de `P`
en une preuve de `Q`. Donc :
- pour **prouver** `P → Q` : `intro hp` (on suppose `P`, on doit montrer `Q`) ;
- pour **utiliser** `hpq : P → Q` avec `hp : P` : `hpq hp` est une preuve de `Q`.

La tactique `exact e` termine le but avec le terme `e` ; `apply h` utilise `h : P → Q`
pour remplacer le but `Q` par le but `P`.

## À prouver
1. `identite : P → P`
2. `modus_ponens : P → (P → Q) → Q`
3. `transitivite : (P → Q) → (Q → R) → (P → R)`

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Propositions and Proofs*.
- [Correspondance de Curry-Howard (Wikipédia)](https://fr.wikipedia.org/wiki/Correspondance_de_Curry-Howard)

---
*Exercice* `Logique.Implication` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Logique.Implication` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem identite : P → P := by
  sorry

theorem modus_ponens : P → (P → Q) → Q := by
  sorry

theorem transitivite : (P → Q) → (Q → R) → (P → R) := by
  sorry

end Parcours.Logique

#verifier
