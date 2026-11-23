/- @parcours
titre: Moins par moins donne plus
difficulte: 3
indice: `mul_zero` : `a * 0 = a * (0 + 0) = a * 0 + a * 0`, puis simplifie avec `add_simpl` (que tu prouves d'abord : si `x + y = x + z` alors `y = z`, en ajoutant `-x` à gauche).
indice: `neg_mul` : montre que `a * b + (-a) * b = 0` (distributivité à droite et `mul_zero`… version à gauche `zero_mul`), puis que l'opposé est unique.
indice: `neg_neg` : `-(-a) = a` par unicité de l'opposé. Puis `(-a) * (-b) = -(a * (-b)) = -(-(a * b)) = a * b`.
-/
import Solutions.Algebre.Definitions

/-!
# Moins par moins donne plus

Pourquoi `(-1) × (-1) = 1` ? Ce n'est pas une convention : c'est une **conséquence** des règles
de calcul (associativité, distributivité…). Prouve-le dans n'importe quel anneau.

Un **anneau** : `+` est un groupe commutatif, `*` est associative avec un neutre `1`,
et `*` est distributive sur `+` des deux côtés.

## À prouver
1. `add_simpl : a + b = a + c → b = c`
2. `mul_zero : a * 0 = 0` et `zero_mul : 0 * a = 0`
3. `neg_unique : a + b = 0 → b = -a`, `neg_neg : -(-a) = a`
4. `neg_mul : (-a) * b = -(a * b)`, `mul_neg : a * (-b) = -(a * b)`
5. `neg_mul_neg : (-a) * (-b) = a * b`
-/

namespace Parcours.Algebre

class Anneau (R : Type) extends Add R, Mul R, Neg R, Zero R, One R where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  neg_add : ∀ a : R, -a + a = 0
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c
  add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c

namespace Anneau

variable {R : Type} [Anneau R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_simpl {a b c : R} (h : a + b = a + c) : b = c := by -- @exo
  calc b = -a + a + b := by rw [neg_add, zero_add]
    _ = -a + (a + c) := by rw [add_assoc, h]
    _ = c := by rw [← add_assoc, neg_add, zero_add]

theorem mul_zero (a : R) : a * 0 = 0 := by -- @exo
  apply add_simpl (a := a * 0)
  rw [← mul_add, zero_add, add_zero]

theorem zero_mul (a : R) : 0 * a = 0 := by -- @exo
  apply add_simpl (a := 0 * a)
  rw [← add_mul, zero_add, add_zero]

theorem neg_unique {a b : R} (h : a + b = 0) : b = -a := by -- @exo
  calc b = -a + a + b := by rw [neg_add, zero_add]
    _ = -a := by rw [add_assoc, h, add_zero]

theorem neg_neg (a : R) : -(-a) = a := by -- @exo
  exact (neg_unique (neg_add a)).symm

theorem neg_mul (a b : R) : (-a) * b = -(a * b) := by -- @exo
  apply neg_unique
  rw [← add_mul, add_comm, neg_add, zero_mul]

theorem mul_neg (a b : R) : a * (-b) = -(a * b) := by -- @exo
  apply neg_unique
  rw [← mul_add, add_comm, neg_add, mul_zero]

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by -- @exo
  rw [neg_mul, mul_neg, neg_neg]

end Anneau
end Parcours.Algebre

#verifier
