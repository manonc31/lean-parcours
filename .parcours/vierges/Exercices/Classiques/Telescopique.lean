import Exercices.Recurrence.Definitions

/-!
# Une somme télescopique

## Se le représenter
`(1² − 0²) + (2² − 1²) + (3² − 2²) + ⋯` : chaque terme annule une partie du précédent, comme un
télescope qu'on replie. Il ne reste que le dernier carré.

## À prouver
`telescopique (n : Nat) : somme (fun i => (i + 1) ^ 2 - i ^ 2) n = n ^ 2`

---
*Exercice* `Classiques.Telescopique` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.Telescopique` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem telescopique (n : Nat) : somme (fun i => (i + 1) ^ 2 - i ^ 2) n = n ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
