/- @parcours
titre: Découper un « et » triple
difficulte: 1
requiert: Gymnase.Constructor
indice: `obtain ⟨hp, hq, hr⟩ := h`.
-/
import ParcoursOutils

/-!
# Découper un « et » triple

`P ∧ Q ∧ R` se lit `P ∧ (Q ∧ R)`. `obtain ⟨hp, hq, hr⟩ := h` découpe tout d'un coup.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem obtain_exemple (P Q R : Prop) (h : P ∧ Q ∧ R) : R := by -- @exo
  obtain ⟨_, _, hr⟩ := h
  exact hr

end Parcours.Gymnase

#verifier
