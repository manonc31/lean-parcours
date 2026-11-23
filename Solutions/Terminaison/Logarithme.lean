/- @parcours
titre: Le logarithme en base 2
difficulte: 3
indice: `fun_induction log2' n with` : un cas `n < 2` et un cas récursif avec `ih` sur `n / 2`.
indice: Cas récursif de `deux_pow_le` : `2 ^ (log2' (n / 2) + 1) = 2 ^ log2' (n / 2) * 2 ≤ (n / 2) * 2 ≤ n`. `Nat.pow_succ` puis `omega` (qui connaît `n / 2`).
indice: Attention : l'hypothèse `1 ≤ n` doit être transmise à l'appel récursif (`1 ≤ n / 2` car `n ≥ 2`).
-/
import Solutions.Recurrence.Definitions

/-!
# Le logarithme en base 2

`log2' n` = le nombre de fois qu'on peut diviser `n` par 2 avant de tomber sous 2.
C'est le nombre de chiffres binaires de `n`, moins 1. C'est aussi le nombre d'étapes d'une
recherche dichotomique dans un tableau de taille `n`.

## À prouver
1. `deux_pow_le : 1 ≤ n → 2 ^ log2' n ≤ n`
2. `lt_deux_pow_succ : n < 2 ^ (log2' n + 1)`
-/

namespace Parcours.Term

def log2' (n : Nat) : Nat :=
  if n < 2 then 0 else log2' (n / 2) + 1
termination_by n
decreasing_by omega

theorem deux_pow_le (n : Nat) (h : 1 ≤ n) : 2 ^ log2' n ≤ n := by -- @exo
  fun_induction log2' n with
  | case1 n _ => simpa using h
  | case2 n hn ih =>
    have := ih (by omega)
    rw [Nat.pow_succ]
    omega

theorem lt_deux_pow_succ (n : Nat) : n < 2 ^ (log2' n + 1) := by -- @exo
  fun_induction log2' n with
  | case1 n hn => simp; omega
  | case2 n hn ih =>
    rw [Nat.pow_succ]
    omega

end Parcours.Term

#verifier
