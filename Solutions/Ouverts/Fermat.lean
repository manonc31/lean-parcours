/- @parcours
titre: Les nombres de Fermat premiers
difficulte: 5
genre: ouvert
requiert: Arithmetique.PetitFermat
indice: Personne au monde ne sait le prouver. Si tu y arrives, publie-le (et préviens-moi) !
indice: Ce que tu PEUX faire : vérifier l'énoncé pour les petites valeurs, avec `decide` ou `#eval`. Essaie !
-/
import Solutions.Arithmetique.Definitions

/-!
# ♾️ Les nombres de Fermat premiers

Fermat pensait que tous les nombres `2^(2^n) + 1` étaient premiers : 3, 5, 17, 257, 65 537. Euler a montré en 1732 que le suivant, 4 294 967 297 = 641 × 6 700 417, ne l'est pas. Depuis, on n'en a trouvé **aucun** autre premier. Conjecture : il n'y en a plus aucun.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Nombre de Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_de_Fermat)
-/

namespace Parcours.Ouverts

open Parcours.Arith

theorem fermat_composes (n : Nat) (hn : 5 ≤ n) : ¬Premier (2 ^ (2 ^ n) + 1) := by -- @exo
  sorry

end Parcours.Ouverts

#verifier
