import Exercices.Arithmetique.RacinePremier
import Exercices.Arithmetique.TestPrimalite

/-!
# √3 est irrationnel

## Se le représenter
Tu as prouvé que `√p` est irrationnel pour tout premier `p`, et tu as un test de primalité.
Assemble les deux !

## À prouver
`racine_trois : ¬∃ a b : Nat, 0 < b ∧ a * a = 3 * (b * b)`

---
*Exercice* `Classiques.Racine3` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.Racine3` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

open Parcours.Arith

theorem racine_trois : ¬∃ a b : Nat, 0 < b ∧ a * a = 3 * (b * b) := by
  sorry

end Parcours.Classiques

#verifier
