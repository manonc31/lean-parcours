/- @parcours
titre: Les valeurs optionnelles
difficulte: 2
requiert: Gymnase.Booleens
indice: `cases o with | none => … | some x => …`.
indice: Cas `none` : `h : none ≠ none`, absurde (`absurd rfl h`).
-/
import ParcoursOutils

/-!
# Les valeurs optionnelles

Une valeur `o : Option Nat` est soit `none` (rien), soit `some x`. Raisonne par cas avec `cases o`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem option_exemple (o : Option Nat) (h : o ≠ none) : ∃ x, o = some x := by -- @exo
  cases o with
  | none => exact absurd rfl h
  | some x => exact ⟨x, rfl⟩

end Parcours.Gymnase

#verifier
