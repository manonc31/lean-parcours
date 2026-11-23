import Exercices.Recurrence.Definitions

/-!
# La somme de Gauss

La légende dit que le petit Gauss, à 9 ans, a calculé `1 + 2 + ⋯ + 100 = 5050` en quelques secondes.
`0 + 1 + 2 + ⋯ + n = n(n+1)/2`.

## À prouver
`gauss (n : Nat) : 2 * somme (fun i => i) (n + 1) = n * (n + 1)`

## Ressources
- [Nombre triangulaire (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_triangulaire)

---
*Exercice* `Recurrence.Gauss` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Recurrence.Gauss` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem gauss (n : Nat) : 2 * somme (fun i => i) (n + 1) = n * (n + 1) := by
  sorry

end Parcours.Recurrence

#verifier
