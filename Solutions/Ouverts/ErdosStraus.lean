/- @parcours
titre: La conjecture d'Erdős–Straus
difficulte: 5
genre: ouvert
requiert: Arithmetique.Bezout
indice: Personne au monde ne sait le prouver. Si tu y arrives, publie-le (et préviens-moi) !
indice: Ce que tu PEUX faire : vérifier l'énoncé pour les petites valeurs, avec `decide` ou `#eval`. Essaie !
-/
import Solutions.Arithmetique.Definitions

/-!
# ♾️ La conjecture d'Erdős–Straus

Pour tout `n ≥ 2`, la fraction `4/n` est la somme de trois fractions égyptiennes : `4/n = 1/x + 1/y + 1/z`. Sans fractions : `4xyz = n(yz + xz + xy)`. Vérifiée jusqu'à 10¹⁷.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Conjecture d'Erdős–Straus (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_d%27Erd%C5%91s-Straus)
-/

namespace Parcours.Ouverts

theorem erdos_straus (n : Nat) (hn : 2 ≤ n) :
    ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ 4 * x * y * z = n * (y * z + x * z + x * y) := by -- @exo
  sorry

end Parcours.Ouverts

#verifier
