/- @parcours
titre: Combien de poignées de main ?
difficulte: 3
requiert: Combinatoire.BinomBase
indice: Récurrence. `binom (n + 1) 2 = binom n 1 + binom n 2 = n + binom n 2` (`binom_succ_succ`, `binom_un`).
indice: Il reste un calcul avec une soustraction : sépare `n = 0` et `n = k + 1`, puis `grind`.
-/
import Solutions.Combinatoire.BinomBase

/-!
# Combien de poignées de main ?

Dans un groupe de `n` personnes, si chacun serre la main de chacun, il y a `C(n, 2) = n(n−1)/2` poignées
de main. Sans division : `2 × C(n, 2) = n(n − 1)`.

## À prouver
`deux_parmi (n : Nat) : 2 * binom n 2 = n * (n - 1)`
-/

namespace Parcours.Combi

theorem deux_parmi (n : Nat) : 2 * binom n 2 = n * (n - 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binom_succ_succ, binom_un, Nat.mul_add, ih, Nat.add_sub_cancel]
    cases n with
    | zero => rfl
    | succ k =>
      rw [Nat.add_sub_cancel]
      grind

end Parcours.Combi

#verifier
