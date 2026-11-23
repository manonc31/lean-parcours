/- @parcours
celebre: 58
titre: La formule des factorielles
difficulte: 4
indice: Récurrence sur `n` en généralisant `k`, puis `cases k`. Le cas `k = 0` est direct.
indice: Cas `n + 1`, `k + 1` : écris `binom (n+1) (k+1) = binom n k + binom n (k+1)` et sépare `k = n` (alors `binom n (n+1) = 0`) et `k < n`.
indice: Si `k < n` : `fact (n - k) = (n - k) * fact (n - k - 1)`. Avec les deux hypothèses de récurrence, la somme vaut `fact n * (k + 1) + fact n * (n - k) = fact n * (n + 1)`.
indice: Utilise `obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m` pour éviter les soustractions, puis `grind`.
-/
import Solutions.Combinatoire.BinomBase

/-!
# La formule des factorielles

`C(n, k) = n! / (k! (n-k)!)`. Sans division : `C(n, k) · k! · (n-k)! = n!`.

## À prouver
`binom_mul_fact : k ≤ n → binom n k * fact k * fact (n - k) = fact n`
-/

namespace Parcours.Combi

theorem binom_mul_fact {n k : Nat} (h : k ≤ n) : binom n k * fact k * fact (n - k) = fact n := by -- @exo
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    cases k with
    | zero => simp [binom_zero_droite, fact_zero]
    | succ k =>
      rw [binom_succ_succ]
      rcases Nat.lt_or_ge k n with hk | hk
      · obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - (k + 1), by omega⟩
        have h1 := ih (k := k) (by omega)
        have h2 := ih (k := k + 1) (by omega)
        rw [show k + 1 + m - k = m + 1 by omega, fact_succ m] at h1
        rw [show k + 1 + m - (k + 1) = m by omega, fact_succ k] at h2
        rw [show k + 1 + m + 1 - (k + 1) = m + 1 by omega, fact_succ k, fact_succ m,
          fact_succ (k + 1 + m)]
        grind
      · have hkn : k = n := by omega
        subst hkn
        have h1 := ih (k := k) (by omega)
        rw [Nat.sub_self, fact_zero, Nat.mul_one] at h1
        rw [binom_eq_zero (show k < k + 1 by omega), Nat.add_zero, Nat.sub_self, fact_zero,
          Nat.mul_one, fact_succ, h1.symm]
        grind

end Parcours.Combi

#verifier
