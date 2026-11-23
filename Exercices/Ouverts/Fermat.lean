import Exercices.Arithmetique.Definitions

/-!
# ♾️ Les nombres de Fermat premiers

Fermat pensait que tous les nombres `2^(2^n) + 1` étaient premiers : 3, 5, 17, 257, 65 537. Euler a montré en 1732 que le suivant, 4 294 967 297 = 641 × 6 700 417, ne l'est pas. Depuis, on n'en a trouvé **aucun** autre premier. Conjecture : il n'y en a plus aucun.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Nombre de Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_de_Fermat)

---
*Exercice* `Ouverts.Fermat` · difficulté ★★★★★

💡 Indices : `./parcours indice Ouverts.Fermat` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Ouverts

open Parcours.Arith

theorem fermat_composes (n : Nat) (hn : 5 ≤ n) : ¬Premier (2 ^ (2 ^ n) + 1) := by
  sorry

end Parcours.Ouverts

#verifier
