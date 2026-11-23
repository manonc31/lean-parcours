import Exercices.Combinatoire.BinomFact
import Exercices.Arithmetique.Definitions

/-!
# Choisir, c'est laisser

Choisir les `k` personnes qui partent en voyage, c'est la même chose que choisir les `n − k` qui
restent : `binom n k = binom n (n − k)`. Le triangle de Pascal est symétrique.

## À prouver
`symetrie : k ≤ n → binom n k = binom n (n - k)`

---
*Exercice* `Combinatoire.Symetrie` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Combinatoire.Symetrie` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

open Parcours.Recurrence

theorem symetrie (n k : Nat) (h : k ≤ n) : binom n k = binom n (n - k) := by
  sorry

end Parcours.Combi

#verifier
