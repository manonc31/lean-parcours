import Exercices.Arithmetique.FacteurPremier

/-!
# Il y a une infinité de nombres premiers

La preuve d'Euclide, vieille de 2300 ans : si `p₁, …, pₖ` étaient tous les premiers,
`p₁⋯pₖ + 1` aurait un facteur premier qui n'est aucun d'eux. Ici on utilise `n! + 1`.

## À prouver
1. `divise_fact : 1 ≤ k → k ≤ n → k ∣ fact n`
2. `infinite_premiers (n : Nat) : ∃ p, n < p ∧ Premier p`

## Ressources
- [Théorème d'Euclide sur les nombres premiers (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_d%27Euclide_sur_les_nombres_premiers)

---
*Exercice* `Arithmetique.InfinitePremiers` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.InfinitePremiers` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

open Parcours.Recurrence

theorem divise_fact {k n : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) : k ∣ fact n := by
  sorry

theorem infinite_premiers (n : Nat) : ∃ p, n < p ∧ Premier p := by
  sorry

end Parcours.Arith

#verifier
