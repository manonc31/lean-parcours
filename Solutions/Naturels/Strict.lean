/- @parcours
titre: L'ordre strict <
difficulte: 3
indice: `lt_irrefl` : `succ a ≤ a` donne `a = succ a + c`… Utilise `le_antisymm` avec `le_succ_self`, puis `succ_ne_self`.
indice: `lt_iff_le_ne`, sens `→` : de `succ a ≤ b`, on a `a ≤ b` (transitivité avec `le_succ_self`), et `a ≠ b` (sinon `lt_irrefl`).
indice: `lt_iff_le_ne`, sens `←` : de `b = a + c` avec `a ≠ b`, `c` ne peut pas être `0` : `cases c`, et si `c = succ d`, `b = succ a + d`.
indice: `zero_lt_succ` : `succ 0 ≤ succ n` découle de `succ_le_succ` et `zero_le`.
-/
import Solutions.Naturels.LeAntisymm
import Solutions.Naturels.LeAdd

/-!
# L'ordre strict

Rappel : `a < b` est défini comme `succ a ≤ b`.

## À prouver
1. `lt_irrefl (a : ℕ) : ¬a < a`
2. `lt_iff_le_ne (a b : ℕ) : a < b ↔ a ≤ b ∧ a ≠ b`
3. `zero_lt_succ (n : ℕ) : 0 < succ n`
4. `not_lt_zero (a : ℕ) : ¬a < 0`
-/

namespace Parcours.ℕ

theorem lt_irrefl (a : ℕ) : ¬a < a := by -- @exo
  intro h
  have h1 : succ a ≤ a := h
  exact succ_ne_self a (le_antisymm _ _ h1 (le_succ_self a))

theorem lt_iff_le_ne (a b : ℕ) : a < b ↔ a ≤ b ∧ a ≠ b := by -- @exo
  constructor
  · intro h
    constructor
    · exact le_trans _ _ _ (le_succ_self a) h
    · intro hab
      rw [hab] at h
      exact lt_irrefl b h
  · rintro ⟨⟨c, hc⟩, hne⟩
    cases c with
    | zero => exact absurd hc.symm hne
    | succ d => exact ⟨d, by rw [hc, add_succ, succ_add]⟩

theorem zero_lt_succ (n : ℕ) : 0 < succ n := by -- @exo
  exact succ_le_succ 0 n (zero_le n)

theorem not_lt_zero (a : ℕ) : ¬a < 0 := by -- @exo
  rintro ⟨c, hc⟩
  rw [succ_add] at hc
  exact zero_ne_succ _ hc

end Parcours.ℕ

#verifier
