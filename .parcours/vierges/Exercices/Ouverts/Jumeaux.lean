import Exercices.Arithmetique.Definitions

/-!
# ♾️ La conjecture des nombres premiers jumeaux

Il existe une infinité de nombres premiers `p` tels que `p + 2` est aussi premier (3 et 5, 11 et 13, 17 et 19…). Yitang Zhang a prouvé en 2013 qu'il y a une infinité de paires de premiers à distance au plus 70 millions ; le projet Polymath a ramené cette distance à 246.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Nombres premiers jumeaux (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_des_nombres_premiers_jumeaux)

---
*Exercice* `Ouverts.Jumeaux` · difficulté ★★★★★

💡 Indices : `./parcours indice Ouverts.Jumeaux` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Ouverts

open Parcours.Arith

theorem jumeaux (N : Nat) : ∃ p, N < p ∧ Premier p ∧ Premier (p + 2) := by
  sorry

end Parcours.Ouverts

#verifier
