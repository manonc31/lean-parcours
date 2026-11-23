import Exercices.Tutoriel.Reecrire

/-!
# Utiliser ses hypothèses

Dans l'infoview, les hypothèses sont listées au-dessus du `⊢`. Par exemple `hp : P` signifie
« `hp` est une preuve de `P` ».

- **`exact e`** : termine le but avec le terme `e` (qui doit avoir exactement le type du but).
- Une hypothèse `hpq : P → Q` est une **fonction** : appliquée à `hp : P`, elle donne `hpq hp : Q`.
- **`apply h`** : si `h : P → Q` et que le but est `Q`, le but devient `P`
  (« pour prouver Q, il suffit de prouver P »).
- **`have h : P := …`** : ajoute un résultat intermédiaire.

## À prouver
1. `utiliser` : de `P` et `P → Q`, déduire `Q`.
2. `chaine` : de `P`, `P → Q` et `Q → R`, déduire `R`.
3. `deux_hypotheses` : de `P`, `Q` et `P → Q → R`, déduire `R`.

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Propositions and Proofs*.

---
*Exercice* `Tutoriel.Hypotheses` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Tutoriel.Hypotheses` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tutoriel

theorem utiliser (P Q : Prop) (hp : P) (hpq : P → Q) : Q := by
  sorry

theorem chaine (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  sorry

theorem deux_hypotheses (P Q R : Prop) (hp : P) (hq : Q) (h : P → Q → R) : R := by
  sorry

end Parcours.Tutoriel

#verifier
