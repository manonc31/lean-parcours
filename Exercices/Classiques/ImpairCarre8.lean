import Exercices.Arithmetique.Definitions

/-!
# Le carré d'un impair modulo 8

## Se le représenter
`1, 9, 25, 49, 81, …` : tous les carrés impairs valent 1 modulo 8. Car `(2n+1)² = 4n(n+1) + 1`,
et `n(n+1)` est pair.

## À prouver
`impair_carre (n : Nat) : ((2 * n + 1) ^ 2) % 8 = 1`

---
*Exercice* `Classiques.ImpairCarre8` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.ImpairCarre8` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem impair_carre (n : Nat) : ((2 * n + 1) ^ 2) % 8 = 1 := by
  sorry

end Parcours.Classiques

#verifier
