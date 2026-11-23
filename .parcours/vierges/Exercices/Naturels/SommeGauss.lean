import Exercices.Naturels.AddMul

/-!
# La somme de Gauss, à la main

`0 + 1 + 2 + ⋯ + n = n(n+1)/2`, sur **ton** ℕ, sans `grind` ni `omega` : seulement tes lemmes
(`add_comm`, `mul_add`, `add_mul`, `mul_comm`…). C'est l'apothéose de la branche ℕ : si tu y
arrives, tu maîtrises le calcul « à la main » dans Lean.

## À prouver
`gauss (n : ℕ) : 2 * somme n = n * succ n`

---
*Exercice* `Naturels.SommeGauss` · difficulté ★★★★☆

💡 Indices : `./parcours indice Naturels.SommeGauss` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

/-- `somme n = 0 + 1 + ⋯ + n` -/
def somme : ℕ → ℕ
  | zero => 0
  | succ n => somme n + succ n

theorem somme_zero : somme 0 = 0 := rfl
theorem somme_succ (n : ℕ) : somme (succ n) = somme n + succ n := rfl

theorem gauss (n : ℕ) : 2 * somme n = n * succ n := by
  sorry

end Parcours.ℕ

#verifier
