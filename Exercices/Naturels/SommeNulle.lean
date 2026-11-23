import Exercices.Naturels.Base

/-!
# Une somme nulle

Dans ℕ, une somme est nulle seulement si les deux termes le sont. (Faux dans ℤ : `1 + (-1) = 0` !)

La tactique **`cases n with`** raisonne par cas : `n = 0` ou `n = succ m`, sans hypothèse de récurrence.

## À prouver
1. `succ_ne_zero (a : ℕ) : succ a ≠ 0`
2. `add_eq_zero (a b : ℕ) : a + b = 0 → a = 0 ∧ b = 0`

---
*Exercice* `Naturels.SommeNulle` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.SommeNulle` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  sorry

theorem add_eq_zero (a b : ℕ) : a + b = 0 → a = 0 ∧ b = 0 := by
  sorry

end Parcours.ℕ

#verifier
