/- @parcours
titre: Sept divise 2³ⁿ − 1
difficulte: 2
requiert: Olympiades.Cinquieme
indice: Récurrence sur `n`.
indice: `2 ^ (3 * (n + 1)) = 2 ^ (3 * n) * 2 ^ 3` (`Nat.pow_add`), puis `Nat.mul_mod` et `ih`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Sept divise 2³ⁿ − 1

`2³ⁿ = 8ⁿ`, et `8 = 7 + 1`… donc `8ⁿ` laisse le reste 1 dans la division par 7.

## À prouver
`sept (n : Nat) : (2 ^ (3 * n)) % 7 = 1`
-/

namespace Parcours.Olymp

theorem sept (n : Nat) : (2 ^ (3 * n)) % 7 = 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 3 by omega, Nat.pow_add, Nat.mul_mod, ih]

end Parcours.Olymp

#verifier
