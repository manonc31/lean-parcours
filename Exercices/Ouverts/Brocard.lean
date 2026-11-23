import Exercices.Arithmetique.Definitions

/-!
# ♾️ Le problème de Brocard

Quand `n! + 1` est-il un carré parfait ? `4! + 1 = 25 = 5²`, `5! + 1 = 121 = 11²`, `7! + 1 = 5041 = 71²`. Brocard (1876) et Ramanujan (1913) ont conjecturé que ce sont les seuls. Vérifié jusqu'à n = 10⁹.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Problème de Brocard (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_de_Brocard)

---
*Exercice* `Ouverts.Brocard` · difficulté ★★★★★

💡 Indices : `./parcours indice Ouverts.Brocard` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Ouverts

open Parcours.Recurrence

theorem brocard (n m : Nat) (h : fact n + 1 = m ^ 2) : n = 4 ∨ n = 5 ∨ n = 7 := by
  sorry

end Parcours.Ouverts

#verifier
