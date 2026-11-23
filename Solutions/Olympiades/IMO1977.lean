/- @parcours
titre: IMO 1977, problème 6
difficulte: 5
genre: boss
solution: non
requiert: Olympiades.IMO1959, Naturels.BonOrdre
indice: Étape 1 : montre par récurrence sur `k` que `∀ n ≥ k, f n ≥ k`. (Utilise l'hypothèse avec `n - 1`.)
indice: Étape 2 : donc `f n ≥ n` pour tout `n`. Et alors `f (n + 1) > f (f n) ≥ f n` : `f` est strictement croissante.
indice: Étape 3 : une fonction strictement croissante vérifie `f (f n) ≥ f n`… combine avec `f (f n) < f (n + 1)` pour obtenir `f n < n + 1`, donc `f n = n`.
-/
import Solutions.Arithmetique.Definitions

/-!
# 💀 IMO 1977, problème 6

> Soit `f : ℕ → ℕ` telle que `f(f(n)) < f(n + 1)` pour tout `n`. Montrer que `f(n) = n` pour tout `n`.

L'un des problèmes les plus célèbres des Olympiades. L'énoncé ne donne presque rien… et pourtant
il force `f` à être l'identité.

Boss sans solution de référence.

## À prouver
`imo1977 (f : Nat → Nat) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n`
-/

namespace Parcours.Olymp

theorem imo1977 (f : Nat → Nat) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by -- @exo
  sorry

end Parcours.Olymp

#verifier
