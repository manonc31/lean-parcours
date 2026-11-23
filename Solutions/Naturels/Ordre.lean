/- @parcours
titre: L'ordre ≤
difficulte: 1
genre: cours
requiert: Naturels.AddComm, Naturels.AddSelf
-/
import Solutions.Naturels.Base

/-!
# L'ordre (cours)

On **définit** `a ≤ b` par : il existe `c` tel que `b = a + c`.
Et `a < b` par : `succ a ≤ b`.

Pour **prouver** `a ≤ b` : donne le `c`, par exemple `exact ⟨c, preuve de b = a + c⟩`.
Pour **utiliser** `h : a ≤ b` : `obtain ⟨c, hc⟩ := h` donne `hc : b = a + c`.

Le symbole `≤` se tape `\le`.

## Ressources
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4), monde « ≤ ».
-/

namespace Parcours.ℕ

/-- `a ≤ b` s'il existe `c` tel que `b = a + c`. -/
def le (a b : ℕ) : Prop := ∃ c, b = a + c

instance : LE ℕ := ⟨le⟩

/-- `a < b` si `succ a ≤ b`. -/
instance : LT ℕ := ⟨fun a b => succ a ≤ b⟩

theorem le_iff_exists_add (a b : ℕ) : a ≤ b ↔ ∃ c, b = a + c := Iff.rfl
theorem lt_iff_succ_le (a b : ℕ) : a < b ↔ succ a ≤ b := Iff.rfl

end Parcours.ℕ
