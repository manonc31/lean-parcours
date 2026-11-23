/- @parcours
titre: Simplifier un produit
difficulte: 4
indice: Récurrence sur `b`, en gardant `c` quelconque : `induction b generalizing c with`. (Sans `generalizing`, l'hypothèse de récurrence ne parlerait que d'un `c` fixé : trop faible !)
indice: Dans chaque cas, raisonne aussi par cas sur `c` (`cases c with`).
indice: Cas `b = 0` : `h : a * 0 = a * c`, donc `a * c = 0`, et `mul_eq_zero` conclut (le cas `a = 0` contredit `ha`).
indice: Cas `succ b` et `succ c` : `h : a * b + a = a * c + a` après `mul_succ`. `add_right_cancel` puis `ih`.
-/
import Solutions.Naturels.MulEqZero
import Solutions.Naturels.Simplification

/-!
# Simplifier un produit (le boss de la multiplication)

Si `a ≠ 0` et `a × b = a × c`, alors `b = c`.

Nouveauté : **`induction b generalizing c with`**. Quand l'énoncé parle d'un `c` quelconque,
il faut que l'hypothèse de récurrence soit vraie pour **tout** `c`, pas seulement pour le `c` du départ.

## À prouver
`mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) : a * b = a * c → b = c`
-/

namespace Parcours.ℕ

theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) : a * b = a * c → b = c := by -- @exo
  induction b generalizing c with
  | zero =>
    intro h
    rw [mul_zero] at h
    rcases mul_eq_zero a c h.symm with h1 | h1
    · exact absurd h1 ha
    · exact h1.symm
  | succ b ih =>
    intro h
    cases c with
    | zero =>
      rw [mul_zero] at h
      rcases mul_eq_zero a (succ b) h with h1 | h1
      · exact absurd h1 ha
      · exact absurd h1 (succ_ne_zero b)
    | succ c =>
      rw [mul_succ, mul_succ] at h
      rw [ih c (add_right_cancel _ _ _ h)]

end Parcours.ℕ

#verifier
