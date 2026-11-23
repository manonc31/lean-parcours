/- @parcours
titre: Divisibilité et ordre
difficulte: 2
indice: `divise_le` : écris `b = a * k`. Si `k = 0` alors `b = 0`, contradiction. Sinon `Nat.le_mul_of_pos_right`.
indice: `divise_antisymm` : sépare les cas `a = 0` et `b = 0` (`Nat.eq_zero_or_pos`), puis utilise `divise_le` deux fois et `Nat.le_antisymm`.
-/
import Solutions.Arithmetique.DiviseBase

/-!
# Divisibilité et ordre

Un diviseur d'un nombre non nul est plus petit que lui. Et la divisibilité est une
relation d'ordre (antisymétrique !) sur les entiers naturels.

## À prouver
1. `divise_le : a ∣ b → 0 < b → a ≤ b`
2. `divise_antisymm : a ∣ b → b ∣ a → a = b`
3. `divise_un : a ∣ 1 → a = 1`
-/

namespace Parcours.Arith

theorem divise_le {a b : Nat} (h : a ∣ b) (hb : 0 < b) : a ≤ b := by -- @exo
  obtain ⟨k, rfl⟩ := h
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · rw [h0, Nat.mul_zero] at hb
    omega
  · exact Nat.le_mul_of_pos_right a h0

theorem divise_antisymm {a b : Nat} (h1 : a ∣ b) (h2 : b ∣ a) : a = b := by -- @exo
  rcases Nat.eq_zero_or_pos a with ha | ha
  · obtain ⟨k, hk⟩ := h1
    rw [hk, ha, Nat.zero_mul]
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · obtain ⟨k, hk⟩ := h2
      rw [hk, hb, Nat.zero_mul]
    · exact Nat.le_antisymm (divise_le h1 hb) (divise_le h2 ha)

theorem divise_un {a : Nat} (h : a ∣ 1) : a = 1 := by -- @exo
  exact divise_antisymm h (un_divise a)

end Parcours.Arith

#verifier
