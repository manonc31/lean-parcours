import Exercices.Arithmetique.Definitions

/-!
# p² − 1 est divisible par 24

> Pour tout nombre premier `p ≥ 5`, `24` divise `p² − 1`.

`5² − 1 = 24`, `7² − 1 = 48`, `11² − 1 = 120`, `13² − 1 = 168`… Un classique des concours.

## À prouver
`premier_carre (hp : Premier p) (h5 : 5 ≤ p) : 24 ∣ p * p - 1`

---
*Exercice* `Olympiades.Premier24` · difficulté ★★★★☆

💡 Indices : `./parcours indice Olympiades.Premier24` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

open Parcours.Arith

theorem premier_carre {p : Nat} (hp : Premier p) (h5 : 5 ≤ p) : 24 ∣ p * p - 1 := by
  sorry

end Parcours.Olymp

#verifier
