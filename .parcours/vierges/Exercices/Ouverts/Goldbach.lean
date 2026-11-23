import Exercices.Arithmetique.Definitions

/-!
# ♾️ La conjecture de Goldbach

Tout entier pair `≥ 4` est la somme de deux nombres premiers. (Goldbach, dans une lettre à Euler en 1742.) Vérifiée jusqu'à 4 × 10¹⁸. Helfgott a prouvé en 2013 la version « faible » (tout impair ≥ 7 est somme de trois premiers).

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Conjecture de Goldbach (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Goldbach)

---
*Exercice* `Ouverts.Goldbach` · difficulté ★★★★★

💡 Indices : `./parcours indice Ouverts.Goldbach` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Ouverts

open Parcours.Arith

theorem goldbach (n : Nat) (h4 : 4 ≤ n) (hpair : n % 2 = 0) :
    ∃ p q, Premier p ∧ Premier q ∧ n = p + q := by
  sorry

end Parcours.Ouverts

#verifier
