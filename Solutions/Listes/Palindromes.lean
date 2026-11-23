/- @parcours
titre: Les palindromes
difficulte: 2
requiert: Listes.Miroir
indice: Deux réécritures suffisent : `miroir_concat` puis `miroir_miroir`.
-/
import Solutions.Listes.Miroir

/-!
# Les palindromes

Un **palindrome** se lit pareil dans les deux sens (« ressasser », `[1, 2, 1]`).
Coller une liste et son miroir donne toujours un palindrome.

## À prouver
`palindrome (l : Liste α) : miroir (l ++ miroir l) = l ++ miroir l`
-/

namespace Parcours.Listes.Liste

theorem palindrome {α : Type} (l : Liste α) : miroir (l ++ miroir l) = l ++ miroir l := by -- @exo
  rw [miroir_concat, miroir_miroir]

end Parcours.Listes.Liste

#verifier
