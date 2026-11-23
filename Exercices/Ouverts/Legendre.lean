import Exercices.Arithmetique.Definitions

/-!
# ♾️ La conjecture de Legendre

Entre deux carrés consécutifs `n²` et `(n + 1)²`, il y a toujours un nombre premier. Le postulat de Bertrand (un premier entre `n` et `2n`) est prouvé, mais celui-ci résiste depuis 1798.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Conjecture de Legendre (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Legendre)

---
*Exercice* `Ouverts.Legendre` · difficulté ★★★★★

💡 Indices : `./parcours indice Ouverts.Legendre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Ouverts

open Parcours.Arith

theorem legendre (n : Nat) (hn : 1 ≤ n) : ∃ p, Premier p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  sorry

end Parcours.Ouverts

#verifier
