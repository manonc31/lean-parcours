/- @parcours
celebre: 1
titre: √2 est irrationnel
difficulte: 3
indice: Lemme de parité : si `a * a` est pair, `a` est pair. Par cas sur `a % 2` (`Nat.mod_two_eq_zero_or_one`), et `Nat.mul_mod` : `(a * a) % 2 = ((a % 2) * (a % 2)) % 2`.
indice: Descente infinie : récurrence forte sur `b`. De `a² = 2b²`, `a` est pair : `a = 2c`, donc `b² = 2c²`. Et `0 < c < b` : c'est une solution plus petite !
indice: Pour `c < b` : sinon `b ≤ c`, donc `b * b ≤ c * c` (`Nat.mul_le_mul`), contradiction avec `b * b = 2 * (c * c)` et `c > 0`.
-/
import Solutions.Arithmetique.Definitions

/-!
# √2 est irrationnel

Si `√2 = a/b`, alors `a² = 2b²`. On montre que c'est impossible (avec `b > 0`), par la
**descente infinie** de Fermat : toute solution en donnerait une plus petite, à l'infini…
ce qui est impossible dans ℕ (c'est une récurrence forte déguisée).

## À prouver
`racine_deux_irrationnelle : ¬∃ a b : Nat, 0 < b ∧ a * a = 2 * (b * b)`

## Ressources
- [Racine carrée de deux (Wikipédia)](https://fr.wikipedia.org/wiki/Racine_carr%C3%A9e_de_deux)
-/

namespace Parcours.Arith

theorem racine_deux_irrationnelle : ¬∃ a b : Nat, 0 < b ∧ a * a = 2 * (b * b) := by -- @exo
  have pair : ∀ a : Nat, (a * a) % 2 = 0 → a % 2 = 0 := by
    intro a h
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · exact h0
    · rw [Nat.mul_mod, h1] at h
      simp at h
  have descente : ∀ b a : Nat, 0 < b → a * a ≠ 2 * (b * b) := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro a hb h
      have ha : a % 2 = 0 := pair a (by rw [h, Nat.mul_mod_right])
      obtain ⟨c, rfl⟩ : ∃ c, a = 2 * c := ⟨a / 2, by omega⟩
      have hbc : b * b = 2 * (c * c) := by grind
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · subst h0
          have := Nat.mul_pos hb hb
          omega
        · exact h0
      have hcb : c < b := by
        apply Classical.byContradiction
        intro hn
        have : b * b ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
        have : 0 < c * c := Nat.mul_pos hc0 hc0
        omega
      exact ih c hcb b hc0 hbc
  rintro ⟨a, b, hb, h⟩
  exact descente b a hb h

end Parcours.Arith

#verifier
