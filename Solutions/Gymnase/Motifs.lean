/- @parcours
titre: Introduire avec un motif
difficulte: 1
requiert: Gymnase.Transfert
indice: `rintro ⟨x, hp, hq⟩` puis `exact ⟨x, hq⟩`.
-/
import ParcoursOutils

/-!
# Introduire avec un motif

`rintro ⟨x, hp, hq⟩` introduit une hypothèse `∃ x, P x ∧ Q x` et la découpe d'un coup.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem motif (P Q : Nat → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x := by -- @exo
  rintro ⟨x, _, hq⟩
  exact ⟨x, hq⟩

end Parcours.Gymnase

#verifier
