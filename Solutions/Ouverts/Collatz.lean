/- @parcours
titre: La conjecture de Syracuse (Collatz)
difficulte: 5
genre: ouvert
requiert: Terminaison.Syracuse
indice: Personne au monde ne sait le prouver. Si tu y arrives, publie-le (et préviens-moi) !
indice: Ce que tu PEUX faire : vérifier l'énoncé pour les petites valeurs, avec `decide` ou `#eval`. Essaie !
-/
import Solutions.Terminaison.Syracuse

/-!
# ♾️ La conjecture de Syracuse (Collatz)

Partant de n'importe quel entier `n ≥ 1`, on applique « si pair, diviser par 2 ; sinon, multiplier par 3 et ajouter 1 ». On finit toujours par atteindre 1 ? Vérifiée jusqu'à environ 2⁷¹. Paul Erdős : « Les mathématiques ne sont pas encore prêtes pour de tels problèmes. » Terence Tao a montré en 2019 que c'est vrai pour « presque tous » les entiers, en un sens précis.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Conjecture de Syracuse (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Syracuse)
-/

namespace Parcours.Ouverts

open Parcours.Term

theorem collatz_conjecture (n : Nat) (hn : 1 ≤ n) : ∃ k, Nat.repeat collatz k n = 1 := by -- @exo
  sorry

end Parcours.Ouverts

#verifier
