/- @parcours
titre: La somme des impairs, à la main
difficulte: 3
requiert: Naturels.SuccMul
indice: Récurrence. `impairs (succ n) = impairs n + (2n + 1)` par définition (`show`).
indice: À droite : `succ n * succ n = n * n + n + succ n` (`mul_succ`, `succ_mul`). À gauche : `two_mul`. Puis réarrange avec `add_assoc` et `add_succ` : il reste une égalité vraie par définition.
-/
import Solutions.Naturels.AddMul

/-!
# La somme des impairs, à la main

`1 + 3 + 5 + ⋯ + (2n − 1) = n²`, sur **ton** ℕ, avec tes lemmes (sans `grind`).

## À prouver
`somme_impairs (n : ℕ) : impairs n = n * n`
-/

namespace Parcours.ℕ

/-- `impairs n = 1 + 3 + ⋯ + (2n - 1)` -/
def impairs : ℕ → ℕ
  | zero => 0
  | succ n => impairs n + (2 * n + 1)

theorem somme_impairs (n : ℕ) : impairs n = n * n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    show impairs n + (2 * n + 1) = succ n * succ n
    rw [ih, mul_succ, succ_mul, two_mul, add_assoc (n * n) n (succ n), add_succ]
    rfl

end Parcours.ℕ

#verifier
