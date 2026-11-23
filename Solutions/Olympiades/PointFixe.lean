/- @parcours
titre: Une équation fonctionnelle
difficulte: 1
requiert: Olympiades.Parite
indice: Applique `h1` à `n` et à `f n`, et `h2` à `n` ; puis `omega`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Une équation fonctionnelle

Soit `f : ℕ → ℕ` telle que `f(n) ≥ n` et `f(f(n)) ≤ n` pour tout `n`. Alors `f` est l'identité !

## Se le représenter
`n ≤ f(n) ≤ f(f(n)) ≤ n` : tout est égal. (La deuxième inégalité vient de la première propriété
appliquée à `f(n)`.)

## À prouver
`point_fixe : (∀ n, n ≤ f n) → (∀ n, f (f n) ≤ n) → ∀ n, f n = n`
-/

namespace Parcours.Olymp

theorem point_fixe (f : Nat → Nat) (h1 : ∀ n, n ≤ f n) (h2 : ∀ n, f (f n) ≤ n) : ∀ n, f n = n := by -- @exo
  intro n
  have a := h1 n
  have b := h1 (f n)
  have c := h2 n
  omega

end Parcours.Olymp

#verifier
