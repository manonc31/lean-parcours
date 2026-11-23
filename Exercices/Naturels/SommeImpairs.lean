import Exercices.Naturels.AddMul

/-!
# La somme des impairs, à la main

`1 + 3 + 5 + ⋯ + (2n − 1) = n²`, sur **ton** ℕ, avec tes lemmes (sans `grind`).

## À prouver
`somme_impairs (n : ℕ) : impairs n = n * n`

---
*Exercice* `Naturels.SommeImpairs` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.SommeImpairs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

/-- `impairs n = 1 + 3 + ⋯ + (2n - 1)` -/
def impairs : ℕ → ℕ
  | zero => 0
  | succ n => impairs n + (2 * n + 1)

theorem somme_impairs (n : ℕ) : impairs n = n * n := by
  sorry

end Parcours.ℕ

#verifier
