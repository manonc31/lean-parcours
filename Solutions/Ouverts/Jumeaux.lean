/- @parcours
titre: La conjecture des nombres premiers jumeaux
difficulte: 5
genre: ouvert
requiert: Arithmetique.InfinitePremiers
indice: Personne au monde ne sait le prouver. Si tu y arrives, publie-le (et préviens-moi) !
indice: Ce que tu PEUX faire : vérifier l'énoncé pour les petites valeurs, avec `decide` ou `#eval`. Essaie !
-/
import Solutions.Arithmetique.Definitions

/-!
# ♾️ La conjecture des nombres premiers jumeaux

Il existe une infinité de nombres premiers `p` tels que `p + 2` est aussi premier (3 et 5, 11 et 13, 17 et 19…). Yitang Zhang a prouvé en 2013 qu'il y a une infinité de paires de premiers à distance au plus 70 millions ; le projet Polymath a ramené cette distance à 246.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Nombres premiers jumeaux (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_des_nombres_premiers_jumeaux)
-/

namespace Parcours.Ouverts

open Parcours.Arith

theorem jumeaux (N : Nat) : ∃ p, N < p ∧ Premier p ∧ Premier (p + 2) := by -- @exo
  sorry

end Parcours.Ouverts

#verifier
