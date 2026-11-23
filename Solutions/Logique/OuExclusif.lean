/- @parcours
titre: Le ou exclusif
difficulte: 2
requiert: Logique.Negation
indice: Déplie la définition avec `obtain ⟨h1, h2⟩ := h` ou `rintro ⟨h1, h2⟩`.
indice: `h.elim Or.inr Or.inl` transforme `P ∨ Q` en `Q ∨ P`.
-/
import ParcoursOutils

/-!
# Le ou exclusif

« Ou bien P, ou bien Q, mais pas les deux » : le **ou exclusif** (XOR).

## À prouver
1. `oux_comm : OuX P Q → OuX Q P`
2. `oux_soi : ¬OuX P P`
3. `oux_faux : OuX P False ↔ P`
-/

namespace Parcours.Logique

def OuX (P Q : Prop) : Prop := (P ∨ Q) ∧ ¬(P ∧ Q)

theorem oux_comm {P Q : Prop} (h : OuX P Q) : OuX Q P := by -- @exo
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1.elim Or.inr Or.inl, fun ⟨hq, hp⟩ => h2 ⟨hp, hq⟩⟩

theorem oux_soi (P : Prop) : ¬OuX P P := by -- @exo
  rintro ⟨h1, h2⟩
  rcases h1 with hp | hp <;> exact h2 ⟨hp, hp⟩

theorem oux_faux (P : Prop) : OuX P False ↔ P := by -- @exo
  constructor
  · rintro ⟨h | h, _⟩
    · exact h
    · exact h.elim
  · intro hp
    exact ⟨Or.inl hp, fun ⟨_, f⟩ => f⟩

end Parcours.Logique

#verifier
