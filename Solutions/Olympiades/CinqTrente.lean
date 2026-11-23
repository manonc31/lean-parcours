/- @parcours
titre: n⁵ − n est divisible par 30
difficulte: 2
requiert: Olympiades.Cinquieme
indice: `Nat.pow_mod : a ^ b % n = (a % n) ^ b % n`.
indice: Puis `generalize n % 30 = r`, `revert r` et `decide` essaie les 30 restes.
indice: Pour la soustraction : `Nat.le_self_pow`.
-/
import Solutions.Arithmetique.Definitions

/-!
# n⁵ − n est divisible par 30

Pour tout entier `n`, `n⁵ − n` est divisible par 2, par 3 et par 5, donc par 30.
La méthode des restes : `n⁵ mod 30` ne dépend que de `n mod 30`, et il n'y a que 30 restes à
essayer.

## À prouver
1. `puissance_cinq_mod : n ^ 5 % 30 = n % 30`
2. `cinq_trente : (n ^ 5 - n) % 30 = 0`
-/

namespace Parcours.Olymp

theorem puissance_cinq_mod (n : Nat) : n ^ 5 % 30 = n % 30 := by -- @exo
  rw [Nat.pow_mod]
  have : n % 30 < 30 := Nat.mod_lt _ (by decide)
  generalize n % 30 = r at this ⊢
  revert r
  decide

theorem cinq_trente (n : Nat) : (n ^ 5 - n) % 30 = 0 := by -- @exo
  have h := puissance_cinq_mod n
  have h2 : n ≤ n ^ 5 := Nat.le_self_pow (by decide) n
  omega

end Parcours.Olymp

#verifier
