/- @parcours
titre: Cinq entiers consécutifs
difficulte: 3
requiert: Olympiades.CinqTrente
indice: `n ≡ n % 120 [mod 120]` (c'est `Nat.mod_mod`).
indice: Combine avec `congru_add` et `congru_mul` pour obtenir la même congruence pour le produit.
indice: Il reste 120 cas : `generalize n % 120 = r`, `revert r`, `decide`.
-/
import Solutions.Arithmetique.Congruences

/-!
# Cinq entiers consécutifs

Le produit de 5 entiers consécutifs est toujours divisible par `5! = 120`. (En général, le produit
de `k` entiers consécutifs est divisible par `k!`, car le quotient est un coefficient binomial.)

Ici, on utilise **tes** lemmes de congruences : chaque facteur est congru à son reste modulo 120,
donc le produit aussi ; et il ne reste que 120 cas à vérifier.

## À prouver
`cinq_consecutifs : (n * (n + 1) * (n + 2) * (n + 3) * (n + 4)) % 120 = 0`
-/

namespace Parcours.Olymp

open Parcours.Arith

theorem cinq_consecutifs (n : Nat) : (n * (n + 1) * (n + 2) * (n + 3) * (n + 4)) % 120 = 0 := by -- @exo
  have h : n ≡ n % 120 [mod 120] := by
    unfold Congru
    exact (Nat.mod_mod _ _).symm
  have h' := congru_mul (congru_mul (congru_mul (congru_mul h (congru_add h (congru_refl 120 1)))
    (congru_add h (congru_refl 120 2))) (congru_add h (congru_refl 120 3)))
    (congru_add h (congru_refl 120 4))
  unfold Congru at h'
  rw [h']
  have : n % 120 < 120 := Nat.mod_lt _ (by decide)
  generalize n % 120 = r at this ⊢
  revert r
  decide

end Parcours.Olymp

#verifier
