import Exercices.Listes.Definitions

/-!
# Concaténer avec la liste vide

Comme `0 + a = a` pour ℕ : un côté est vrai par définition, l'autre demande une récurrence.

## À prouver
`concat_nil (l : Liste α) : l ++ nil = l`

---
*Exercice* `Listes.ConcatNil` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Listes.ConcatNil` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

theorem concat_nil {α : Type} (l : Liste α) : l ++ nil = l := by
  sorry

end Parcours.Listes.Liste

#verifier
