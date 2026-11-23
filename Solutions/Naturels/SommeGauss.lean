/- @parcours
titre: La somme de Gauss, à la main
difficulte: 4
requiert: Naturels.PowMul
indice: Récurrence sur `n`. Le cas `zero` : `2 * somme 0 = 2 * 0 = 0 = 0 * 1` (`mul_zero`, `zero_mul`).
indice: Cas `succ n` : `somme (succ n) = somme n + succ n`, donc `2 * somme (succ n) = 2 * somme n + 2 * succ n = n * succ n + 2 * succ n` (`mul_add`, `ih`).
indice: Il reste `n * succ n + 2 * succ n = succ n * succ (succ n)`. Fais apparaître `succ n` en facteur (`← add_mul`), retourne le produit de droite (`mul_comm`), puis `congr 1` : il reste `n + 2 = succ (succ n)`, vrai par définition.
-/
import Solutions.Naturels.AddMul

/-!
# La somme de Gauss, à la main

`0 + 1 + 2 + ⋯ + n = n(n+1)/2`, sur **ton** ℕ, sans `grind` ni `omega` : seulement tes lemmes
(`add_comm`, `mul_add`, `add_mul`, `mul_comm`…). C'est l'apothéose de la branche ℕ : si tu y
arrives, tu maîtrises le calcul « à la main » dans Lean.

## À prouver
`gauss (n : ℕ) : 2 * somme n = n * succ n`
-/

namespace Parcours.ℕ

/-- `somme n = 0 + 1 + ⋯ + n` -/
def somme : ℕ → ℕ
  | zero => 0
  | succ n => somme n + succ n

theorem somme_zero : somme 0 = 0 := rfl
theorem somme_succ (n : ℕ) : somme (succ n) = somme n + succ n := rfl

theorem gauss (n : ℕ) : 2 * somme n = n * succ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, mul_add, ih, ← add_mul, mul_comm (succ n) (succ (succ n))]
    congr 1

end Parcours.ℕ

#verifier
