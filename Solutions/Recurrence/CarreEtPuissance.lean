/- @parcours
titre: n² contre 2ⁿ
difficulte: 3
requiert: Recurrence.Croissance
indice: Écris `n = k + 4` (`obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩`) et fais une récurrence sur `k`.
indice: Pas de récurrence : `(k+5)² = (k+4)² + 2(k+4) + 1 ≤ 2·(k+4)² ≤ 2·2^(k+4)`. Établis `2(k+4) + 1 ≤ (k+4)²` avec `grind`, puis `omega`.
-/
import Solutions.Recurrence.Definitions

/-!
# n² contre 2ⁿ

Pour `n ≥ 4`, `n² ≤ 2ⁿ` : l'exponentielle finit toujours par battre le polynôme.
(Faux pour `n = 3` : `9 > 8`.)

## À prouver
`carre_le_puissance (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ 2 ^ n`
-/

namespace Parcours.Recurrence

theorem carre_le_puissance (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by -- @exo
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  clear h
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 2 * (k + 4) + 1 ≤ (k + 4) ^ 2 := by grind
    rw [show k + 1 + 4 = (k + 4) + 1 by omega, Nat.pow_succ 2]
    have h2 : (k + 4 + 1) ^ 2 = (k + 4) ^ 2 + 2 * (k + 4) + 1 := by grind
    omega

end Parcours.Recurrence

#verifier
