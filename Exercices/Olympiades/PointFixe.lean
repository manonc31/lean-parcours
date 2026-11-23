import Exercices.Arithmetique.Definitions

/-!
# Une équation fonctionnelle

Soit `f : ℕ → ℕ` telle que `f(n) ≥ n` et `f(f(n)) ≤ n` pour tout `n`. Alors `f` est l'identité !

## Se le représenter
`n ≤ f(n) ≤ f(f(n)) ≤ n` : tout est égal. (La deuxième inégalité vient de la première propriété
appliquée à `f(n)`.)

## À prouver
`point_fixe : (∀ n, n ≤ f n) → (∀ n, f (f n) ≤ n) → ∀ n, f n = n`

---
*Exercice* `Olympiades.PointFixe` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Olympiades.PointFixe` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem point_fixe (f : Nat → Nat) (h1 : ∀ n, n ≤ f n) (h2 : ∀ n, f (f n) ≤ n) : ∀ n, f n = n := by
  sorry

end Parcours.Olymp

#verifier
