import Exercices.Naturels.Base

/-!
# Associativité de l'addition

`(a + b) + c = a + (b + c)`. En Lean, `a + b + c` se lit `(a + b) + c`.

## À prouver
`add_assoc (a b c : ℕ) : a + b + c = a + (b + c)`

## Rappel
- `add_zero a : a + 0 = a`
- `add_succ a b : a + succ b = succ (a + b)`

---
*Exercice* `Naturels.AddAssoc` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.AddAssoc` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  sorry

end Parcours.ℕ

#verifier
