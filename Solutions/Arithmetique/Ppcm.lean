/- @parcours
titre: Le PPCM
difficulte: 3
requiert: Arithmetique.PgcdMul
indice: `Nat.mul_div_cancel' (h : n ∣ m) : n * (m / n) = m`. Il faut donc montrer que `pgcd a b` divise `a * b`.
indice: `Nat.mul_div_assoc a (h : k ∣ b) : a * b / k = a * (b / k)`.
-/
import Solutions.Arithmetique.PgcdDivise

/-!
# Le PPCM

Le plus petit commun multiple : `ppcm a b = a × b / pgcd a b`. (Les lemmes de division de `Nat`
sont permis : `Nat.mul_div_cancel'`, `Nat.mul_div_assoc`.)

## À prouver
1. `pgcd_mul_ppcm : pgcd a b * ppcm a b = a * b`
2. `divise_ppcm : a ∣ ppcm a b`
-/

namespace Parcours.Arith

def ppcm (a b : Nat) : Nat := a * b / pgcd a b

theorem pgcd_mul_ppcm (a b : Nat) : pgcd a b * ppcm a b = a * b := by -- @exo
  unfold ppcm
  exact Nat.mul_div_cancel' (divise_mul_droite (pgcd_divise a b).1 b)

theorem divise_ppcm (a b : Nat) : a ∣ ppcm a b := by -- @exo
  unfold ppcm
  rw [Nat.mul_div_assoc a (pgcd_divise a b).2]
  exact ⟨b / pgcd a b, rfl⟩

end Parcours.Arith

#verifier
