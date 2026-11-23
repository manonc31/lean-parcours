/- @parcours
titre: La conjecture de Legendre
difficulte: 5
genre: ouvert
requiert: Arithmetique.InfinitePremiers
indice: Personne au monde ne sait le prouver. Si tu y arrives, publie-le (et préviens-moi) !
indice: Ce que tu PEUX faire : vérifier l'énoncé pour les petites valeurs, avec `decide` ou `#eval`. Essaie !
-/
import Solutions.Arithmetique.Definitions

/-!
# ♾️ La conjecture de Legendre

Entre deux carrés consécutifs `n²` et `(n + 1)²`, il y a toujours un nombre premier. Le postulat de Bertrand (un premier entre `n` et `2n`) est prouvé, mais celui-ci résiste depuis 1798.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Conjecture de Legendre (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Legendre)
-/

namespace Parcours.Ouverts

open Parcours.Arith

theorem legendre (n : Nat) (hn : 1 ≤ n) : ∃ p, Premier p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by -- @exo
  sorry

end Parcours.Ouverts

#verifier
