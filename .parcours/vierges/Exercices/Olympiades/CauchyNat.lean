import Exercices.Arithmetique.Definitions

/-!
# L'équation de Cauchy

Une équation fonctionnelle : trouver toutes les fonctions `f : ℕ → ℕ` telles que
`f(x + y) = f(x) + f(y)` pour tous `x, y`. Réponse : les fonctions linéaires `f(n) = n × f(1)`.

## À prouver
`cauchy_nat : (∀ x y, f (x + y) = f x + f y) → ∀ n, f n = n * f 1`

---
*Exercice* `Olympiades.CauchyNat` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.CauchyNat` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem cauchy_nat (f : Nat → Nat) (h : ∀ x y, f (x + y) = f x + f y) : ∀ n, f n = n * f 1 := by
  sorry

end Parcours.Olymp

#verifier
