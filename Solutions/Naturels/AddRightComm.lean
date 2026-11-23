/- @parcours
titre: Échanger des termes
difficulte: 2
indice: Pas besoin de récurrence : seulement `add_assoc` et `add_comm`.
indice: `rw [add_assoc, add_comm b c, ← add_assoc]`.
indice: Attention : `rw [add_comm]` tout seul réécrit la PREMIÈRE addition qu'il trouve. Précise les arguments : `add_comm b c`.
-/
import Solutions.Naturels.AddComm
import Solutions.Naturels.AddAssoc

/-!
# Échanger des termes

Avec l'associativité et la commutativité, on peut réordonner une somme comme on veut.
Mais attention : `rw [add_comm]` réécrit la **première** somme qu'il voit. Pour viser une somme
précise, donne les arguments : `rw [add_comm b c]`.

## À prouver
1. `add_right_comm (a b c : ℕ) : a + b + c = a + c + b`
2. `add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c)`
-/

namespace Parcours.ℕ

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by -- @exo
  rw [add_assoc, add_comm b c, ← add_assoc]

theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by -- @exo
  rw [← add_assoc, add_comm a b, add_assoc]

end Parcours.ℕ

#verifier
