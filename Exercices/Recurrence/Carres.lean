import Exercices.Recurrence.Definitions

/-!
# La somme des carrés

`0² + 1² + ⋯ + n² = n(n+1)(2n+1)/6`.

## À prouver
`somme_carres (n : Nat) : 6 * somme (fun i => i ^ 2) (n + 1) = n * (n + 1) * (2 * n + 1)`

---
*Exercice* `Recurrence.Carres` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.Carres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem somme_carres (n : Nat) :
    6 * somme (fun i => i ^ 2) (n + 1) = n * (n + 1) * (2 * n + 1) := by
  sorry

end Parcours.Recurrence

#verifier
