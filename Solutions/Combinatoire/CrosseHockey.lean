/- @parcours
titre: La crosse de hockey
difficulte: 2
requiert: Combinatoire.SommeLigne
indice: Récurrence sur `m`. Le cas de base : `binom k k = 1` (`binom_self`).
indice: Pas de récurrence : la formule de Pascal `binom_succ_succ` sur `binom (m + k + 2) (k + 1)`.
-/
import Solutions.Combinatoire.BinomBase

/-!
# La crosse de hockey

Dans le triangle de Pascal, additionne les nombres d'une diagonale, en partant du bord :
`1 + 3 + 6 + 10 = 20`. Le résultat est juste en dessous, décalé d'un cran : la figure dessine une
**crosse de hockey**.

## À prouver
`crosse_hockey : somme (fun i => binom (i + k) k) (m + 1) = binom (m + k + 1) (k + 1)`

## Ressources
- [Identité de la crosse de hockey (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Hockey-stick_identity)
-/

namespace Parcours.Combi

open Parcours.Recurrence

theorem crosse_hockey (k m : Nat) :
    somme (fun i => binom (i + k) k) (m + 1) = binom (m + k + 1) (k + 1) := by -- @exo
  induction m with
  | zero =>
    simp only [somme_succ, Nat.zero_add]
    rw [binom_self, binom_self]
    rfl
  | succ m ih =>
    rw [somme_succ, ih, show m + 1 + k + 1 = (m + k + 1) + 1 by omega, binom_succ_succ (m + k + 1) k,
      show m + 1 + k = m + k + 1 by omega]
    omega

end Parcours.Combi

#verifier
