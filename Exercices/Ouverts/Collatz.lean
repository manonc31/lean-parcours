import Exercices.Terminaison.Syracuse

/-!
# ♾️ La conjecture de Syracuse (Collatz)

Partant de n'importe quel entier `n ≥ 1`, on applique « si pair, diviser par 2 ; sinon, multiplier par 3 et ajouter 1 ». On finit toujours par atteindre 1 ? Vérifiée jusqu'à environ 2⁷¹. Paul Erdős : « Les mathématiques ne sont pas encore prêtes pour de tels problèmes. » Terence Tao a montré en 2019 que c'est vrai pour « presque tous » les entiers, en un sens précis.

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Conjecture de Syracuse (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Syracuse)

---
*Exercice* `Ouverts.Collatz` · difficulté ★★★★★

💡 Indices : `./parcours indice Ouverts.Collatz` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Ouverts

open Parcours.Term

theorem collatz_conjecture (n : Nat) (hn : 1 ≤ n) : ∃ k, Nat.repeat collatz k n = 1 := by
  sorry

end Parcours.Ouverts

#verifier
