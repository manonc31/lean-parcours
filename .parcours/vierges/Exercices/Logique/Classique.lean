import Exercices.Logique.DeMorgan

/-!
# La logique classique

Jusqu'ici tout était **constructif**. La logique classique ajoute le **tiers exclu** :
pour toute proposition `P`, `P ∨ ¬P`. En Lean : `Classical.em P : P ∨ ¬P`.

C'est un **axiome** (en réalité, Lean le déduit de l'axiome du choix — voir l'exercice
« Diaconescu »). Il est autorisé dès maintenant.

Tactique pratique : `by_cases h : P` crée deux cas, l'un avec `h : P`, l'autre avec `h : ¬P`.
Aussi : `Classical.byContradiction` (raisonnement par l'absurde) :
`apply Classical.byContradiction` puis `intro h` te donne `h : ¬(but)` et le but `False`.

## À prouver
1. `double_neg_elim : ¬¬P → P`
2. `non_et : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q`
3. `contraposee_inverse : (¬Q → ¬P) → (P → Q)`
4. `impl_ou : (P → Q) ↔ ¬P ∨ Q`

## Ressources
- [Principe du tiers exclu (Wikipédia)](https://fr.wikipedia.org/wiki/Principe_du_tiers_exclu)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), section *Classical Logic*.

---
*Exercice* `Logique.Classique` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Logique.Classique` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem double_neg_elim (h : ¬¬P) : P := by
  sorry

theorem non_et : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

theorem contraposee_inverse (h : ¬Q → ¬P) : P → Q := by
  sorry

theorem impl_ou : (P → Q) ↔ ¬P ∨ Q := by
  sorry

end Parcours.Logique

#verifier
