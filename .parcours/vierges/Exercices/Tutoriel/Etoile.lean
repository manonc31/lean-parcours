import Exercices.Tutoriel.Hypotheses

/-!
# Gagner ta première étoile ⭐

La bibliothèque de Lean contient déjà des milliers de théorèmes. Par exemple, `Nat.zero_add n`
est une preuve de `0 + n = n`. Mais le but de ce parcours est de **tout reconstruire toi-même**.

D'où la règle des étoiles :
- ✅ **réussi** : la preuve est correcte, mais elle utilise des théorèmes de la bibliothèque
  que tu n'as pas encore « débloqués ».
- ⭐ **pur** : la preuve n'utilise que tes propres résultats (et les mécanismes de base : `rfl`,
  `rw`, `induction`, `exact`…).

Plus tard, des exercices **Pont** 🌉 (par exemple « mon ℕ fait maison est le même que le `Nat` de Lean »)
débloqueront officiellement des pans de la bibliothèque pour les exercices qui en dépendent.

## À prouver
1. `sans_la_bibliotheque` : `0 + n = n`, **par récurrence**, sans aucun lemme.
2. `avec_la_bibliotheque` : la même chose. Commence par la prouver avec `exact Nat.zero_add n`,
   et regarde le message de `#verifier` : ✅ mais pas ⭐ !

Ta première récurrence ! La tactique `induction n with` découpe la preuve en deux cas :
- `zero` : prouver la propriété pour `0` ;
- `succ m ih` : prouver la propriété pour `m + 1`, en sachant qu'elle est vraie pour `m`
  (c'est l'hypothèse de récurrence `ih`).

En Lean, `a + (b + 1)` est **par définition** égal à `(a + b) + 1` : c'est comme ça que
l'addition de `Nat` est programmée (récursivement sur le second argument).
La tactique `show` permet de remplacer le but par un but égal *par définition*.

⚠️ Pour avoir l'étoile, **chaque** théorème du fichier doit être pur : tu devras donc
finalement réécrire aussi `avec_la_bibliotheque`… sans la bibliothèque (indice : tu viens de prouver la même chose !).

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Induction and Recursion*.

---
*Exercice* `Tutoriel.Etoile` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Tutoriel.Etoile` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tutoriel

theorem sans_la_bibliotheque (n : Nat) : 0 + n = n := by
  sorry

theorem avec_la_bibliotheque (n : Nat) : 0 + n = n := by
  sorry

end Parcours.Tutoriel

#verifier
