/- @parcours
titre: L'équation de Cauchy
difficulte: 2
requiert: Olympiades.IMO1977
indice: Commence par `f 0` : `h 0 0` dit `f 0 = f 0 + f 0`.
indice: Puis récurrence : `f (n + 1) = f n + f 1`.
-/
import Solutions.Arithmetique.Definitions

/-!
# L'équation de Cauchy

Une équation fonctionnelle : trouver toutes les fonctions `f : ℕ → ℕ` telles que
`f(x + y) = f(x) + f(y)` pour tous `x, y`. Réponse : les fonctions linéaires `f(n) = n × f(1)`.

## À prouver
`cauchy_nat : (∀ x y, f (x + y) = f x + f y) → ∀ n, f n = n * f 1`
-/

namespace Parcours.Olymp

theorem cauchy_nat (f : Nat → Nat) (h : ∀ x y, f (x + y) = f x + f y) : ∀ n, f n = n * f 1 := by -- @exo
  intro n
  induction n with
  | zero =>
    have := h 0 0
    simp at this
    simp
    omega
  | succ n ih => rw [h n 1, ih, Nat.succ_mul]

end Parcours.Olymp

#verifier
