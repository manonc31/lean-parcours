/- @parcours
titre: Onze divise 10²ⁿ⁺¹ + 1
difficulte: 3
requiert: Olympiades.Sept
indice: Récurrence. `10 ^ (2(n+1)+1) = 10 ^ (2n+1) * 100`.
indice: Comme `100 = 99 + 1` et `99 = 9 × 11`, `omega` sait conclure à partir de l'hypothèse de récurrence.
-/
import Solutions.Arithmetique.Definitions

/-!
# Onze divise 10²ⁿ⁺¹ + 1

`11`, `1001 = 7 × 11 × 13`, `100001 = 11 × 9091`… Les nombres `10^(2n+1) + 1` sont tous divisibles par 11.
(Critère de divisibilité par 11 : `10 ≡ −1` modulo 11.)

## À prouver
`onze (n : Nat) : (10 ^ (2 * n + 1) + 1) % 11 = 0`
-/

namespace Parcours.Olymp

theorem onze (n : Nat) : (10 ^ (2 * n + 1) + 1) % 11 = 0 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, Nat.pow_add]
    have : (10 : Nat) ^ 2 = 100 := rfl
    rw [this]
    omega

end Parcours.Olymp

#verifier
