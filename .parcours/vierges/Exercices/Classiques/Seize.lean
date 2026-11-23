import Exercices.Arithmetique.Definitions

/-!
# Les puissances de 16 et le chiffre 5

## Se le représenter
`16 = 15 + 1`, donc toutes les puissances de 16 valent 1 modulo 5 (et se terminent par 6 en base 10 !).

## À prouver
`seize (n : Nat) : (16 ^ n) % 5 = 1`

---
*Exercice* `Classiques.Seize` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.Seize` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem seize (n : Nat) : (16 ^ n) % 5 = 1 := by
  sorry

end Parcours.Classiques

#verifier
