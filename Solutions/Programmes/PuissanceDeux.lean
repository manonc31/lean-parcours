/- @parcours
titre: Est-ce une puissance de 2 ?
difficulte: 2
requiert: Programmes.Popcount
indice: `rw [estPuissance2]` déplie la définition ; puis simplifie le `if`.
indice: Pour la réciproque : `fun_induction estPuissance2 n`. Dans le cas récursif, `n / 2 = 2^k` et `n` pair donnent `n = 2^(k+1)`.
-/
import Solutions.Programmes.Definitions

/-!
# Est-ce une puissance de 2 ?

Pour tester si `n` est une puissance de 2 : on divise par 2 tant que c'est pair, et on regarde
si on arrive à 1.

## À prouver
1. `puissance_ok : estPuissance2 (2 ^ k) = true`
2. `puissance_correct : estPuissance2 n = true → ∃ k, n = 2 ^ k`
-/

namespace Parcours.Prog

def estPuissance2 (n : Nat) : Bool :=
  if n ≤ 1 then n == 1 else n % 2 == 0 && estPuissance2 (n / 2)
termination_by n
decreasing_by omega

theorem puissance_ok (k : Nat) : estPuissance2 (2 ^ k) = true := by -- @exo
  induction k with
  | zero => rw [estPuissance2]; simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [estPuissance2]
    simp only [show ¬ 2 ^ (k + 1) ≤ 1 by rw [Nat.pow_succ]; omega, ↓reduceIte]
    rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide), ih]
    simp

theorem puissance_correct (n : Nat) (h : estPuissance2 n = true) : ∃ k, n = 2 ^ k := by -- @exo
  fun_induction estPuissance2 n with
  | case1 n hn =>
    exact ⟨0, by simp at h; omega⟩
  | case2 n hn ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨k, hk⟩ := ih h.2
    exact ⟨k + 1, by rw [Nat.pow_succ]; omega⟩

end Parcours.Prog

#verifier
