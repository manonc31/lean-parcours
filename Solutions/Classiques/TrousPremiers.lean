/- @parcours
titre: Des déserts de nombres premiers
difficulte: 3
requiert: Arithmetique.InfinitePremiers
indice: `divise_fact : 1 ≤ k → k ≤ n → k ∣ fact n`, et `divise_add`.
indice: Un premier n'a que 1 et lui-même comme diviseurs ; or `1 < k < (n+1)! + k`.
indice: Pour `mille` : `m = 1001! + 2`.
-/
import Solutions.Arithmetique.InfinitePremiers

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
-/

namespace Parcours.Classiques

open Parcours.Arith Parcours.Recurrence

theorem desert (n k : Nat) (h1 : 2 ≤ k) (h2 : k ≤ n + 1) : ¬ Premier (fact (n + 1) + k) := by -- @exo
  intro ⟨_, hp⟩
  have hd : k ∣ fact (n + 1) + k := divise_add (divise_fact (by omega) h2) (divise_refl k)
  rcases hp k hd with h | h
  · omega
  · have := fact_pos (n + 1)
    omega

theorem mille : ∃ m, ∀ i, i < 1000 → ¬ Premier (m + i) := by -- @exo
  refine ⟨fact 1001 + 2, fun i hi => ?_⟩
  rw [Nat.add_assoc]
  exact desert 1000 (2 + i) (by omega) (by omega)

end Parcours.Classiques

#verifier
