import Exercices.Naturels.Multiplication
import Exercices.Naturels.AddAssoc

/-!
# Distributivité de × sur +

`a × (b + c) = a × b + a × c`. Le pont entre l'addition et la multiplication.

## À prouver
`mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c`

---
*Exercice* `Naturels.MulAdd` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.MulAdd` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  sorry

end Parcours.ℕ

#verifier
