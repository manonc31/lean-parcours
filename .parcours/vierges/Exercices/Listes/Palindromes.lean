import Exercices.Listes.Miroir

/-!
# Les palindromes

Un **palindrome** se lit pareil dans les deux sens (« ressasser », `[1, 2, 1]`).
Coller une liste et son miroir donne toujours un palindrome.

## À prouver
`palindrome (l : Liste α) : miroir (l ++ miroir l) = l ++ miroir l`

---
*Exercice* `Listes.Palindromes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Listes.Palindromes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

theorem palindrome {α : Type} (l : Liste α) : miroir (l ++ miroir l) = l ++ miroir l := by
  sorry

end Parcours.Listes.Liste

#verifier
