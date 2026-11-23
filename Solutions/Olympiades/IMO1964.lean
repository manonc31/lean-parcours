/- @parcours
titre: IMO 1964, problème 1
difficulte: 3
requiert: Olympiades.Sept
indice: Pour le lemme : récurrence, `Nat.pow_succ` et `Nat.mul_mod`, puis découpe tous les `if` avec `repeat' split` et conclus avec `all_goals omega`.
indice: Pour le théorème : `2 ^ n ≥ 1` (`Nat.one_le_two_pow`) ; découpe les cas du lemme avec `repeat' split at h`, puis `omega` dans chacun (`all_goals omega`).
-/
import Solutions.Arithmetique.Definitions

/-!
# IMO 1964, problème 1

> Trouver tous les entiers `n` tels que `2ⁿ − 1` est divisible par 7.

Réponse : exactement les multiples de 3. La suite des restes de `2ⁿ` modulo 7 est périodique :
`1, 2, 4, 1, 2, 4, …`

## À prouver
1. `reste_puissance_deux : 2 ^ n % 7 = (si n % 3 = 0 alors 1 sinon si n % 3 = 1 alors 2 sinon 4)`
2. `imo1964 (n : Nat) : (2 ^ n - 1) % 7 = 0 ↔ n % 3 = 0`
-/

namespace Parcours.Olymp

theorem reste_puissance_deux (n : Nat) :
    2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    repeat' split
    all_goals omega

theorem imo1964 (n : Nat) : (2 ^ n - 1) % 7 = 0 ↔ n % 3 = 0 := by -- @exo
  have h := reste_puissance_deux n
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  repeat' split at h
  all_goals omega

end Parcours.Olymp

#verifier
