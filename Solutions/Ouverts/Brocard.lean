/- @parcours
titre: Le problème de Brocard
difficulte: 5
genre: ouvert
requiert: Arithmetique.InfinitePremiers
indice: Personne au monde ne sait le prouver. Si tu y arrives, publie-le (et préviens-moi) !
indice: Ce que tu PEUX faire : vérifier l'énoncé pour les petites valeurs, avec `decide` ou `#eval`. Essaie !
-/
import Solutions.Arithmetique.Definitions

/-!
# ♾️ Le problème de Brocard

Quand `n! + 1` est-il un carré parfait ? `4! + 1 = 25 = 5²`, `5! + 1 = 121 = 11²`, `7! + 1 = 5041 = 71²`. Brocard (1876) et Ramanujan (1913) ont conjecturé que ce sont les seuls. Vérifié jusqu'à n = 10⁹.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Problème de Brocard (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_de_Brocard)
-/

namespace Parcours.Ouverts

open Parcours.Recurrence

theorem brocard (n m : Nat) (h : fact n + 1 = m ^ 2) : n = 4 ∨ n = 5 ∨ n = 7 := by -- @exo
  sorry

end Parcours.Ouverts

#verifier
