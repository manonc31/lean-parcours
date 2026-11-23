import Exercices.Naturels.AddComm
import Exercices.Naturels.AddAssoc

/-!
# Échanger des termes

Avec l'associativité et la commutativité, on peut réordonner une somme comme on veut.
Mais attention : `rw [add_comm]` réécrit la **première** somme qu'il voit. Pour viser une somme
précise, donne les arguments : `rw [add_comm b c]`.

## À prouver
1. `add_right_comm (a b c : ℕ) : a + b + c = a + c + b`
2. `add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c)`

---
*Exercice* `Naturels.AddRightComm` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.AddRightComm` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  sorry

theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  sorry

end Parcours.ℕ

#verifier
