import Exercices.Naturels.Multiplication
import Exercices.Naturels.AddRightComm

/-!
# Successeur à gauche, version multiplicative

`(a + 1) × b = a × b + b`. C'est la clé de la commutativité de la multiplication.

## À prouver
`succ_mul (a b : ℕ) : succ a * b = a * b + b`

---
*Exercice* `Naturels.SuccMul` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.SuccMul` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  sorry

end Parcours.ℕ

#verifier
