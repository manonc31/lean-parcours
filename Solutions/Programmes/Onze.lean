/- @parcours
titre: La règle de divisibilité par 11
difficulte: 3
requiert: Programmes.Chiffres
indice: `fun_induction alterne n`. Dans le cas récursif, `n = 10 * (n / 10) + n % 10` : `omega` voit tout seul que la différence est un multiple de 11.
indice: `omega` connaît les conversions `Nat → Int` et les `%` par des constantes.
-/
import Solutions.Programmes.Definitions

/-!
# La règle de divisibilité par 11

Pour savoir si un nombre est divisible par 11, on fait la somme **alternée** de ses chiffres en
partant des unités : `918082 → 2 − 8 + 0 − 8 + 1 − 9 = −22`, divisible par 11, donc 918082 aussi.
Pourquoi ? Parce que `10 ≡ −1 (mod 11)`.

## À prouver
1. `onze_alterne : (n - alterne n) % 11 = 0` (dans `Int`)
2. `onze_divise : n % 11 = 0 ↔ alterne n % 11 = 0`
-/

namespace Parcours.Prog

def alterne (n : Nat) : Int := if n < 10 then n else ((n % 10 : Nat) : Int) - alterne (n / 10)
termination_by n
decreasing_by omega

theorem onze_alterne (n : Nat) : ((n : Int) - alterne n) % 11 = 0 := by -- @exo
  fun_induction alterne n with
  | case1 n _ => simp
  | case2 n _ ih => omega

theorem onze_divise (n : Nat) : n % 11 = 0 ↔ alterne n % 11 = 0 := by -- @exo
  have := onze_alterne n
  omega

end Parcours.Prog

#verifier
