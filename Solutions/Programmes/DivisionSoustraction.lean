/- @parcours
titre: Diviser en soustrayant
difficulte: 2
requiert: Programmes.Russe
indice: `fun_induction divSous a b` : un cas « on peut soustraire », un cas « on s'arrête ».
indice: Dans le premier cas : `(q + 1) * b = q * b + b` (`Nat.add_mul`), puis `omega`.
indice: Pour le quotient : réécris `a` en `q * b + r`, puis `Nat.add_mul_div_right` et `Nat.div_eq_of_lt`.
-/
import Solutions.Programmes.Definitions

/-!
# Diviser en soustrayant

Comment diviser quand on ne sait que soustraire ? On retire `b` de `a` tant qu'on peut, en
comptant les retraits : le nombre de retraits est le quotient, ce qui reste est le reste.

## À prouver
1. `divSous_spec : q * b + r = a ∧ r < b` où `(q, r) = divSous a b` (si `b > 0`)
2. `divSous_quotient : (divSous a b).1 = a / b`
-/

namespace Parcours.Prog

def divSous (a b : Nat) : Nat × Nat :=
  if _ : 0 < b ∧ b ≤ a then ((divSous (a - b) b).1 + 1, (divSous (a - b) b).2) else (0, a)
termination_by a
decreasing_by omega

theorem divSous_spec (a b : Nat) (hb : 0 < b) :
    (divSous a b).1 * b + (divSous a b).2 = a ∧ (divSous a b).2 < b := by -- @exo
  fun_induction divSous a b with
  | case1 a h ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only
    rw [Nat.add_mul, Nat.one_mul]
    omega
  | case2 a h =>
    dsimp only
    omega

theorem divSous_quotient (a b : Nat) (hb : 0 < b) : (divSous a b).1 = a / b := by -- @exo
  obtain ⟨h1, h2⟩ := divSous_spec a b hb
  conv => rhs; rw [← h1]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt h2, Nat.zero_add]

end Parcours.Prog

#verifier
