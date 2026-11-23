/- @parcours
titre: La somme des produits consécutifs
difficulte: 2
requiert: Recurrence.Carres
indice: Récurrence ; `somme_succ`, `Nat.mul_add`, l'hypothèse de récurrence, puis `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# La somme des produits consécutifs

## Se le représenter
`1·2 + 2·3 + 3·4 + ⋯ + n(n+1) = n(n+1)(n+2)/3`. Visuellement : des « boîtes » `i × (i+1)` qui
s'empilent en une pyramide dont le volume est un tiers d'un pavé.

## À prouver
`produits_consecutifs (n : Nat) : 3 * somme (fun i => i * (i + 1)) (n + 1) = n * (n + 1) * (n + 2)`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem produits_consecutifs (n : Nat) :
    3 * somme (fun i => i * (i + 1)) (n + 1) = n * (n + 1) * (n + 2) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.mul_add, ih]
    grind

end Parcours.Classiques

#verifier
