/- @parcours
titre: L'ordre est total
difficulte: 3
indice: Récurrence sur `b`. Cas `zero` : `right` et `zero_le`.
indice: Cas `succ b` : `rcases ih with ⟨c, hc⟩ | ⟨c, hc⟩`. Si `a ≤ b` (b = a + c), alors `a ≤ succ b` avec `succ c`.
indice: Si `b ≤ a` (a = b + c), raisonne par cas sur `c` : si `c = 0`, alors `a = b ≤ succ b` ; si `c = succ d`, alors `a = succ b + d` (`succ_add`), donc `succ b ≤ a`.
-/
import Solutions.Naturels.LeBase
import Solutions.Naturels.SuccAdd

/-!
# L'ordre est total

Deux entiers sont toujours comparables : `a ≤ b` ou `b ≤ a`.

## À prouver
`le_total (a b : ℕ) : a ≤ b ∨ b ≤ a`
-/

namespace Parcours.ℕ

theorem le_total (a b : ℕ) : a ≤ b ∨ b ≤ a := by -- @exo
  induction b with
  | zero => exact Or.inr (zero_le a)
  | succ b ih =>
    rcases ih with ⟨c, hc⟩ | ⟨c, hc⟩
    · left
      exact ⟨succ c, by rw [hc, add_succ]⟩
    · cases c with
      | zero =>
        left
        exact ⟨1, by rw [hc]; rfl⟩
      | succ d =>
        right
        exact ⟨d, by rw [hc, add_succ, succ_add]⟩

end Parcours.ℕ

#verifier
