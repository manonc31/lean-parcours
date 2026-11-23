/- @parcours
titre: √p est irrationnel
difficulte: 4
indice: Même descente infinie que pour √2, mais au lieu de la parité, utilise le lemme d'Euclide : `p ∣ a * a` donc `p ∣ a`.
indice: Écris `a = p * c` ; alors `p * p * (c * c) = p * (b * b)`, donc `b * b = p * (c * c)` (simplifier par `p > 0` : `Nat.eq_of_mul_eq_mul_left`).
indice: Pour `c < b` : si `b ≤ c` alors `b * b ≤ c * c < p * (c * c)` car `p ≥ 2`.
-/
import Solutions.Arithmetique.LemmeEuclide

/-!
# √p est irrationnel

Généralisation : pour tout nombre premier `p`, `√p` est irrationnel.

## À prouver
`racine_premier_irrationnelle (hp : Premier p) : ¬∃ a b : Nat, 0 < b ∧ a * a = p * (b * b)`
-/

namespace Parcours.Arith

theorem racine_premier_irrationnelle {p : Nat} (hp : Premier p) :
    ¬∃ a b : Nat, 0 < b ∧ a * a = p * (b * b) := by -- @exo
  have hp2 := hp.1
  have descente : ∀ b a : Nat, 0 < b → a * a ≠ p * (b * b) := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro a hb h
      have hpa : p ∣ a := by
        have : p ∣ a * a := ⟨b * b, h⟩
        rcases premier_divise_mul hp this with h1 | h1 <;> exact h1
      obtain ⟨c, rfl⟩ := hpa
      have hbc : b * b = p * (c * c) := by
        apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < p)
        rw [← h]
        grind
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · subst h0
          have := Nat.mul_pos hb hb
          omega
        · exact h0
      have hcb : c < b := by
        apply Classical.byContradiction
        intro hn
        have h1 : b * b ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
        have h2 : 2 * (c * c) ≤ p * (c * c) := Nat.mul_le_mul_right _ hp2
        have : 0 < c * c := Nat.mul_pos hc0 hc0
        omega
      exact ih c hcb b hc0 hbc
  rintro ⟨a, b, hb, h⟩
  exact descente b a hb h

end Parcours.Arith

#verifier
