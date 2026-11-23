import Exercices.Naturels.MulComm
import Exercices.Naturels.MulAdd
import Exercices.Naturels.MulAssoc

/-!
# Distributivité à droite

## À prouver
1. `add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c`
2. `two_mul (a : ℕ) : 2 * a = a + a`
3. `mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c)`

---
*Exercice* `Naturels.AddMul` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.AddMul` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  sorry

theorem two_mul (a : ℕ) : 2 * a = a + a := by
  sorry

theorem mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  sorry

end Parcours.ℕ

#verifier
