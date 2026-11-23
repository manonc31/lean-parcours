import Exercices.Naturels.Simplification
import Exercices.Naturels.SommeNulle

/-!
# Ajouter sans changer

Si `a + b = a`, alors `b = 0`. Et un entier n'est jamais égal à son successeur.

## À prouver
1. `add_right_eq_self (a b : ℕ) : a + b = a → b = 0`
2. `succ_ne_self (n : ℕ) : succ n ≠ n`

---
*Exercice* `Naturels.AddSelf` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.AddSelf` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem add_right_eq_self (a b : ℕ) : a + b = a → b = 0 := by
  sorry

theorem succ_ne_self (n : ℕ) : succ n ≠ n := by
  sorry

end Parcours.ℕ

#verifier
