import Exercices.Arithmetique.Definitions

/-!
# 💀 IMO 1977, problème 6

> Soit `f : ℕ → ℕ` telle que `f(f(n)) < f(n + 1)` pour tout `n`. Montrer que `f(n) = n` pour tout `n`.

L'un des problèmes les plus célèbres des Olympiades. L'énoncé ne donne presque rien… et pourtant
il force `f` à être l'identité.

Boss sans solution de référence.

## À prouver
`imo1977 (f : Nat → Nat) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n`

---
*Exercice* `Olympiades.IMO1977` · difficulté ★★★★★

💡 Indices : `./parcours indice Olympiades.IMO1977` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem imo1977 (f : Nat → Nat) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by
  sorry

end Parcours.Olymp

#verifier
