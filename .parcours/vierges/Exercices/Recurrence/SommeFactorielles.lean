import Exercices.Recurrence.Definitions

/-!
# Une somme de factorielles

`0·0! + 1·1! + 2·2! + ⋯ + n·n! = (n+1)! − 1`. (Joli : `1 + 4 + 18 = 23 = 4! − 1`.)

## À prouver
`somme_factorielles (n : Nat) : somme (fun k => k * fact k) (n + 1) + 1 = fact (n + 1)`

---
*Exercice* `Recurrence.SommeFactorielles` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.SommeFactorielles` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem somme_factorielles (n : Nat) : somme (fun k => k * fact k) (n + 1) + 1 = fact (n + 1) := by
  sorry

end Parcours.Recurrence

#verifier
