import Exercices.Recurrence.Definitions

/-!
# La somme des impairs

`1 + 3 + 5 + ⋯ + (2n - 1) = n²`. Un dessin le montre : des équerres qui s'emboîtent en carré.

## À prouver
`somme_impairs (n : Nat) : somme (fun i => 2 * i + 1) n = n ^ 2`

---
*Exercice* `Recurrence.Impairs` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Recurrence.Impairs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem somme_impairs (n : Nat) : somme (fun i => 2 * i + 1) n = n ^ 2 := by
  sorry

end Parcours.Recurrence

#verifier
