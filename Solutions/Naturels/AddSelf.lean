/- @parcours
titre: Ajouter sans changer
difficulte: 2
indice: `add_right_eq_self` : réécris le `a` de droite en `a + 0` (`rw [← add_zero a]` en visant bien… ou plus simple : `apply add_left_cancel a`), puis conclus.
indice: Concrètement : `have h' : a + b = a + 0 := h` (c'est vrai par définition), puis `exact add_left_cancel a b 0 h'`.
indice: `succ_ne_self` : `succ n = n + 1`, donc `succ n = n` donnerait `1 = 0`.
-/
import Solutions.Naturels.Simplification
import Solutions.Naturels.SommeNulle

/-!
# Ajouter sans changer

Si `a + b = a`, alors `b = 0`. Et un entier n'est jamais égal à son successeur.

## À prouver
1. `add_right_eq_self (a b : ℕ) : a + b = a → b = 0`
2. `succ_ne_self (n : ℕ) : succ n ≠ n`
-/

namespace Parcours.ℕ

theorem add_right_eq_self (a b : ℕ) : a + b = a → b = 0 := by -- @exo
  intro h
  have h' : a + b = a + 0 := h
  exact add_left_cancel a b 0 h'

theorem succ_ne_self (n : ℕ) : succ n ≠ n := by -- @exo
  intro h
  have h1 : n + 1 = n := h
  have h2 := add_right_eq_self n 1 h1
  rw [one_eq_succ_zero] at h2
  exact succ_ne_zero 0 h2

end Parcours.ℕ

#verifier
