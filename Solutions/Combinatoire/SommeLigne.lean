/- @parcours
titre: La somme d'une ligne du triangle
difficulte: 3
indice: Lemme clé (Pascal sur les sommes) : `somme (binom (n+1)) (m+1) = somme (binom n) (m+1) + somme (binom n) m`. Prouve-le par récurrence sur `m`.
indice: Pour le théorème, récurrence sur `n` : `somme (binom (n+1)) (n+2) = somme (binom n) (n+2) + somme (binom n) (n+1)`, et `somme (binom n) (n+2) = somme (binom n) (n+1)` car `binom n (n+1) = 0`.
-/
import Solutions.Combinatoire.BinomBase

/-!
# La somme d'une ligne du triangle

`C(n,0) + C(n,1) + ⋯ + C(n,n) = 2ⁿ` : c'est le nombre total de parties d'un ensemble à `n` éléments.

## À prouver
1. `somme_pascal : somme (binom (n + 1)) (m + 1) = somme (binom n) (m + 1) + somme (binom n) m`
2. `somme_ligne (n : Nat) : somme (binom n) (n + 1) = 2 ^ n`
-/

namespace Parcours.Combi

theorem somme_pascal (n m : Nat) :
    somme (binom (n + 1)) (m + 1) = somme (binom n) (m + 1) + somme (binom n) m := by -- @exo
  induction m with
  | zero =>
    show somme (binom (n + 1)) 0 + binom (n + 1) 0 = somme (binom n) 0 + binom n 0 + 0
    rw [binom_zero_droite, binom_zero_droite]
    rfl
  | succ m ih =>
    rw [somme_succ (binom (n + 1)), ih, binom_succ_succ, somme_succ (binom n) (m + 1),
      somme_succ (binom n) m]
    omega

theorem somme_ligne (n : Nat) : somme (binom n) (n + 1) = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_pascal, somme_succ (binom n) (n + 1), binom_eq_zero (by omega), ih, Nat.pow_succ]
    omega

end Parcours.Combi

#verifier
