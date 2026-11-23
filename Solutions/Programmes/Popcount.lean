/- @parcours
titre: Compter les bits à 1
difficulte: 2
requiert: Programmes.Chiffres
indice: Pour déplier une fonction définie avec `termination_by`, utilise `rw [bits1]` (pas `rfl`).
indice: Ensuite les deux lemmes `bits1_double` et `bits1_double_un` suffisent pour tout le reste.
indice: `2^(k+1) − 1 = 2 × (2^k − 1) + 1`.
-/
import Solutions.Programmes.Definitions

/-!
# Compter les bits à 1

Combien de `1` dans l'écriture binaire de `n` ? (Les processeurs ont une instruction exprès,
`popcount`.) On regarde le dernier bit (`n % 2`) et on recommence avec `n / 2`.

## À prouver
1. `bits1_double : bits1 (2 * n) = bits1 n` et `bits1_double_un : bits1 (2 * n + 1) = bits1 n + 1`
2. `bits1_puissance : bits1 (2 ^ k) = 1` (`100…0`)
3. `bits1_mersenne : bits1 (2 ^ k - 1) = k` (`11…1`)
-/

namespace Parcours.Prog

def bits1 (n : Nat) : Nat := if n = 0 then 0 else n % 2 + bits1 (n / 2)
termination_by n
decreasing_by omega

theorem bits1_zero : bits1 0 = 0 := by -- @exo
  rw [bits1]
  simp

theorem bits1_double (n : Nat) : bits1 (2 * n) = bits1 n := by -- @exo
  by_cases h : n = 0
  · subst h
    simp [bits1_zero]
  · have h' : 2 * n ≠ 0 := by omega
    rw [bits1]
    simp only [h', ↓reduceIte]
    rw [show 2 * n % 2 = 0 by omega, show 2 * n / 2 = n by omega, Nat.zero_add]

theorem bits1_double_un (n : Nat) : bits1 (2 * n + 1) = bits1 n + 1 := by -- @exo
  rw [bits1]
  simp only [show 2 * n + 1 ≠ 0 by omega, ↓reduceIte]
  rw [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]
  omega

theorem bits1_puissance (k : Nat) : bits1 (2 ^ k) = 1 := by -- @exo
  induction k with
  | zero =>
    rw [Nat.pow_zero, show (1 : Nat) = 2 * 0 + 1 from rfl, bits1_double_un, bits1_zero]
  | succ k ih => rw [Nat.pow_succ, Nat.mul_comm, bits1_double, ih]

theorem bits1_mersenne (k : Nat) : bits1 (2 ^ k - 1) = k := by -- @exo
  induction k with
  | zero => simp [bits1_zero]
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      rw [Nat.pow_succ]
      omega
    rw [h, bits1_double_un, ih]

end Parcours.Prog

#verifier
