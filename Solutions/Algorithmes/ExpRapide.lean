/- @parcours
titre: L'exponentiation rapide
difficulte: 3
indice: `fun_induction expRapide a n with` : trois cas (`n = 0`, `n` pair, `n` impair).
indice: Cas pair : `(a * a) ^ (n / 2) = a ^ (2 * (n / 2))` grâce à `← Nat.pow_two` et `← Nat.pow_mul`. Et `2 * (n / 2) = n` quand `n` est pair (`omega`).
indice: Cas impair : `a * a ^ (2 * (n / 2)) = a ^ (2 * (n / 2) + 1)` (`← Nat.pow_succ'`).
-/
import Solutions.Algorithmes.Definitions

/-!
# L'exponentiation rapide

Calculer `aⁿ` en multipliant `n` fois prend `n` étapes. L'exponentiation rapide utilise
`a^(2k) = (a²)^k` et `a^(2k+1) = a · (a²)^k` : seulement `log₂ n` étapes ! Pour `n` = 1 milliard,
c'est 30 multiplications au lieu d'un milliard. Utilisée partout en cryptographie (RSA).

## À prouver
`expRapide_eq (a n : Nat) : expRapide a n = a ^ n`
-/

namespace Parcours.Algo

def expRapide (a n : Nat) : Nat :=
  if n = 0 then 1
  else if n % 2 = 0 then expRapide (a * a) (n / 2)
  else a * expRapide (a * a) (n / 2)
termination_by n
decreasing_by all_goals omega

theorem expRapide_eq (a n : Nat) : expRapide a n = a ^ n := by -- @exo
  fun_induction expRapide a n with
  | case1 a => rfl
  | case2 a n h1 h2 ih =>
    rw [ih, ← Nat.pow_two, ← Nat.pow_mul]
    congr 1
    omega
  | case3 a n h1 h2 ih =>
    rw [ih, ← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ']
    congr 1
    omega

end Parcours.Algo

#verifier
