import ParcoursOutils

/-!
# Le théorème de Diaconescu

L'**axiome du choix** dit que dans toute famille d'ensembles non vides, on peut choisir un élément
de chacun. En Lean : `Classical.choose (h : ∃ x, p x)` est un `x` vérifiant `p`
(`Classical.choose_spec h : p (Classical.choose h)`).

Le théorème de Diaconescu (1975) : **l'axiome du choix implique le tiers exclu** (avec l'extensionnalité
des fonctions `funext` et des propositions `propext`). C'est exactement comme ça que Lean définit
`Classical.em` !

Ici tu as droit à `Classical.choose`, `Classical.choose_spec`, `funext`, `propext`,
mais **pas** au tiers exclu ni à `by_cases` (le vérificateur le refuserait).

## À prouver
`diaconescu (P : Prop) : P ∨ ¬P`

## Ressources
- [Théorème de Diaconescu (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Axioms and Computation*.

---
*Exercice* `Logique.Diaconescu` · difficulté ★★★★☆

💡 Indices : `./parcours indice Logique.Diaconescu` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem diaconescu (P : Prop) : P ∨ ¬P := by
  sorry

end Parcours.Logique

#verifier
