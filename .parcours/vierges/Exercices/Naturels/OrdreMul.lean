import Exercices.Naturels.LeBase
import Exercices.Naturels.MulAdd

/-!
# Ordre et multiplication

La multiplication respecte l'ordre : si `a ≤ b`, alors `c × a ≤ c × b`.

## À prouver
1. `le_add_right : a ≤ a + b`
2. `mul_le_mul_left : a ≤ b → c * a ≤ c * b`

---
*Exercice* `Naturels.OrdreMul` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.OrdreMul` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem le_add_right (a b : ℕ) : a ≤ a + b := by
  sorry

theorem mul_le_mul_left (a b c : ℕ) (h : a ≤ b) : c * a ≤ c * b := by
  sorry

end Parcours.ℕ

#verifier
