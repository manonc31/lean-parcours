import ParcoursOutils

/-!
# Les valeurs optionnelles

Une valeur `o : Option Nat` est soit `none` (rien), soit `some x`. Raisonne par cas avec `cases o`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Option` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Option` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem option_exemple (o : Option Nat) (h : o ≠ none) : ∃ x, o = some x := by
  sorry

end Parcours.Gymnase

#verifier
