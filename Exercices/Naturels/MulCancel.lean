import Exercices.Naturels.MulEqZero
import Exercices.Naturels.Simplification

/-!
# Simplifier un produit (le boss de la multiplication)

Si `a ≠ 0` et `a × b = a × c`, alors `b = c`.

Nouveauté : **`induction b generalizing c with`**. Quand l'énoncé parle d'un `c` quelconque,
il faut que l'hypothèse de récurrence soit vraie pour **tout** `c`, pas seulement pour le `c` du départ.

## À prouver
`mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) : a * b = a * c → b = c`

---
*Exercice* `Naturels.MulCancel` · difficulté ★★★★☆

💡 Indices : `./parcours indice Naturels.MulCancel` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) : a * b = a * c → b = c := by
  sorry

end Parcours.ℕ

#verifier
