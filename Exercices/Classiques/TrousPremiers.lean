import Exercices.Arithmetique.InfinitePremiers

/-!
# Des déserts de nombres premiers

## Se le représenter
Il y a une infinité de nombres premiers, mais aussi des « déserts » aussi longs qu'on veut :
`(n+1)! + 2, (n+1)! + 3, …, (n+1)! + (n+1)` sont `n` entiers consécutifs **tous composés**,
car `k` divise `(n+1)! + k` pour `2 ≤ k ≤ n + 1`. Par exemple, il existe 1000 entiers consécutifs
dont aucun n'est premier.

## À prouver
1. `desert : 2 ≤ k → k ≤ n + 1 → ¬ Premier (fact (n + 1) + k)`
2. `mille : ∃ m, ∀ i, i < 1000 → ¬ Premier (m + i)`

---
*Exercice* `Classiques.TrousPremiers` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Classiques.TrousPremiers` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Arith Parcours.Recurrence

theorem desert (n k : Nat) (h1 : 2 ≤ k) (h2 : k ≤ n + 1) : ¬ Premier (fact (n + 1) + k) := by
  sorry

theorem mille : ∃ m, ∀ i, i < 1000 → ¬ Premier (m + i) := by
  sorry

end Parcours.Classiques

#verifier
