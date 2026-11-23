import Exercices.Recurrence.Definitions

/-!
# La moyenne est entre les deux

## Se le représenter
La moyenne de deux nombres est entre les deux (ici avec la division entière).

## À prouver
`moyenne : a ≤ b → a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b`, et `max_min : max a b + min a b = a + b`

---
*Exercice* `Classiques.Moyenne` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.Moyenne` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem moyenne (a b : Nat) (h : a ≤ b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by
  sorry

theorem max_min (a b : Nat) : max a b + min a b = a + b := by
  sorry

end Parcours.Classiques

#verifier
