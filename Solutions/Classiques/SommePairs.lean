/- @parcours
titre: La somme des nombres pairs
difficulte: 1
requiert: Recurrence.Impairs
indice: Récurrence, `somme_succ`, puis `grind` (avec l'hypothèse de récurrence dans le contexte).
-/
import Solutions.Recurrence.Definitions

/-!
# La somme des nombres pairs

## Se le représenter
Empile les nombres pairs `0, 2, 4, …, 2(n−1)` en colonnes de points : tu obtiens un rectangle
`n × (n − 1)` (deux escaliers identiques collés). Donc la somme vaut `n(n − 1)`.

## À prouver
`somme_pairs (n : Nat) : somme (fun i => 2 * i) n + n = n * n` (c'est-à-dire `n(n − 1)`, sans soustraction)
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem somme_pairs (n : Nat) : somme (fun i => 2 * i) n + n = n * n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ]
    grind

end Parcours.Classiques

#verifier
