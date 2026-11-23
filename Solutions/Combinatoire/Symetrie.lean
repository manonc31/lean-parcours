/- @parcours
titre: Choisir, c'est laisser
difficulte: 2
requiert: Combinatoire.BinomFact
indice: Utilise la formule `binom_mul_fact` pour `k` et pour `n − k`.
indice: Les deux produits valent `n!` ; on simplifie par `k! (n − k)! > 0` (`Nat.eq_of_mul_eq_mul_right`).
-/
import Solutions.Combinatoire.BinomFact
import Solutions.Arithmetique.Definitions

/-!
# Choisir, c'est laisser

Choisir les `k` personnes qui partent en voyage, c'est la même chose que choisir les `n − k` qui
restent : `binom n k = binom n (n − k)`. Le triangle de Pascal est symétrique.

## À prouver
`symetrie : k ≤ n → binom n k = binom n (n - k)`
-/

namespace Parcours.Combi

open Parcours.Recurrence

theorem symetrie (n k : Nat) (h : k ≤ n) : binom n k = binom n (n - k) := by -- @exo
  have h1 := binom_mul_fact h
  have h2 := binom_mul_fact (Nat.sub_le n k)
  rw [Nat.sub_sub_self h] at h2
  have hp : 0 < fact k * fact (n - k) := Nat.mul_pos (Parcours.Arith.fact_pos k) (Parcours.Arith.fact_pos (n - k))
  apply Nat.eq_of_mul_eq_mul_right hp
  grind

end Parcours.Combi

#verifier
