import Exercices.Arithmetique.Definitions

/-!
# Un carré est pair ssi…

## Se le représenter
Si `n` est impair, `n × n` aussi (impair × impair = impair). C'est l'argument clé de l'irrationalité de √2.

## À prouver
`carre_pair (n : Nat) : (n * n) % 2 = 0 ↔ n % 2 = 0`

---
*Exercice* `Classiques.CarrePair` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.CarrePair` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem carre_pair (n : Nat) : (n * n) % 2 = 0 ↔ n % 2 = 0 := by
  sorry

end Parcours.Classiques

#verifier
