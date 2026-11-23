/- @parcours
titre: Premières valeurs du triangle
difficulte: 2
indice: `binom_eq_zero` : récurrence sur `n` en généralisant `k`, puis `cases k`. Pour `n + 1` et `k + 1` : `binom_succ_succ`, et les deux termes sont nuls par hypothèse de récurrence.
indice: `binom_self` : récurrence ; `binom_succ_succ`, `ih` et `binom_eq_zero` (car `n < n + 1`).
indice: `binom_un` : récurrence ; `binom_succ_succ`, `binom_zero_droite`, `ih`, puis `omega`.
-/
import Solutions.Combinatoire.Definitions

/-!
# Premières valeurs du triangle

## À prouver
1. `binom_eq_zero : n < k → binom n k = 0`
2. `binom_self (n : Nat) : binom n n = 1`
3. `binom_un (n : Nat) : binom n 1 = n`
-/

namespace Parcours.Combi

theorem binom_eq_zero {n k : Nat} (h : n < k) : binom n k = 0 := by -- @exo
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [binom_succ_succ, ih (by omega), ih (by omega)]

theorem binom_self (n : Nat) : binom n n = 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [binom_succ_succ, ih, binom_eq_zero (by omega)]

theorem binom_un (n : Nat) : binom n 1 = n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binom_succ_succ, binom_zero_droite, ih]
    omega

end Parcours.Combi

#verifier
