import ParcoursOutils

/-!
# by_cases : vrai ou faux ?

`by_cases h : P` crée deux cas : un avec `h : P`, l'autre avec `h : ¬P`. (Logique classique.)

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.ParCas` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.ParCas` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem par_cas (P Q : Prop) (h1 : P → Q) (h2 : ¬P → Q) : Q := by
  sorry

end Parcours.Gymnase

#verifier
