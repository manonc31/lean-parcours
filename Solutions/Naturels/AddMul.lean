/- @parcours
titre: Distributivité à droite
difficulte: 2
indice: Utilise `mul_comm` pour te ramener à `mul_add`.
indice: `rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]`.
indice: `two_mul` : `rw [two_eq_succ_one, succ_mul, one_mul]`.
-/
import Solutions.Naturels.MulComm
import Solutions.Naturels.MulAdd
import Solutions.Naturels.MulAssoc

/-!
# Distributivité à droite

## À prouver
1. `add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c`
2. `two_mul (a : ℕ) : 2 * a = a + a`
3. `mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c)`
-/

namespace Parcours.ℕ

theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by -- @exo
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

theorem two_mul (a : ℕ) : 2 * a = a + a := by -- @exo
  rw [two_eq_succ_one, succ_mul, one_mul]

theorem mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c) := by -- @exo
  rw [← mul_assoc, mul_comm a b, mul_assoc]

end Parcours.ℕ

#verifier
