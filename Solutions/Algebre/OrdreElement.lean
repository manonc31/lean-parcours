/- @parcours
titre: Puissances et ordre d'un élément
difficulte: 2
requiert: Algebre.Puissances
indice: Récurrences sur l'exposant, avec `puiss_succ` et `puiss_add`.
indice: `puiss_ordre` se déduit des deux premiers.
-/
import Solutions.Algebre.Puissances

/-!
# Puissances et ordre d'un élément

Si `aⁿ = 1`, alors toutes les puissances `a^(n·k)` valent aussi 1. (Le plus petit tel `n > 0` s'appelle
l'**ordre** de `a`.)

## À prouver
1. `un_puiss : (1 : G) ^ k = 1`
2. `puiss_mul : a ^ (m * n) = (a ^ m) ^ n`
3. `puiss_ordre : a ^ n = 1 → a ^ (n * k) = 1`
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem un_puiss (k : Nat) : (1 : G) ^ k = 1 := by -- @exo
  induction k with
  | zero => rfl
  | succ k ih => rw [puiss_succ, ih, Groupe.one_mul]

theorem puiss_mul (a : G) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, puiss_add, ih, puiss_succ]

theorem puiss_ordre {a : G} {n : Nat} (h : a ^ n = 1) (k : Nat) : a ^ (n * k) = 1 := by -- @exo
  rw [puiss_mul, h, un_puiss]

end Parcours.Algebre

#verifier
