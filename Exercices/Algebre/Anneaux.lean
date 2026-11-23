import Exercices.Algebre.Definitions

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

---
*Exercice* `Algebre.Anneaux` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algebre.Anneaux` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

theorem add_simpl {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem mul_zero (a : R) : a * 0 = 0 := by
  sorry

theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry

theorem neg_unique {a b : R} (h : a + b = 0) : b = -a := by
  sorry

theorem neg_neg (a : R) : -(-a) = a := by
  sorry

theorem neg_mul (a b : R) : (-a) * b = -(a * b) := by
  sorry

theorem mul_neg (a b : R) : a * (-b) = -(a * b) := by
  sorry

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  sorry

end Anneau
end Parcours.Algebre

#verifier
