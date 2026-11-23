/- @parcours
titre: PGCD et multiplication
difficulte: 3
indice: `fun_induction pgcd a b with`. Cas `case1 a` : `pgcd (a * c) (0 * c) = a * c` (`Nat.zero_mul`, `pgcd_zero`).
indice: Cas `case2` : si `c = 0` tout vaut `0`. Sinon, `b * c ≠ 0` (`Nat.mul_ne_zero`), donc `pgcd_rec` s'applique, et `Nat.mul_mod_mul_right : x * z % (y * z) = x % y * z` fait apparaître l'hypothèse de récurrence.
-/
import Solutions.Arithmetique.PgcdDivise

/-!
# PGCD et multiplication

`pgcd (a·c) (b·c) = pgcd a b · c`. Ce petit lemme est la clé du lemme de Gauss.

## À prouver
`pgcd_mul_droite (a b c : Nat) : pgcd (a * c) (b * c) = pgcd a b * c`
-/

namespace Parcours.Arith

theorem pgcd_mul_droite (a b c : Nat) : pgcd (a * c) (b * c) = pgcd a b * c := by -- @exo
  fun_induction pgcd a b with
  | case1 a => rw [Nat.zero_mul, pgcd_zero]
  | case2 a b hb ih =>
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      simp only [Nat.mul_zero]
      rw [pgcd_zero]
    · rw [pgcd_rec (a * c) (b * c) (Nat.mul_ne_zero hb (by omega)), Nat.mul_mod_mul_right, ih]

end Parcours.Arith

#verifier
