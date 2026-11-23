import Exercices.Arithmetique.Definitions

/-!
# Sept divise 2³ⁿ − 1

`2³ⁿ = 8ⁿ`, et `8 = 7 + 1`… donc `8ⁿ` laisse le reste 1 dans la division par 7.

## À prouver
`sept (n : Nat) : (2 ^ (3 * n)) % 7 = 1`

---
*Exercice* `Olympiades.Sept` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.Sept` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem sept (n : Nat) : (2 ^ (3 * n)) % 7 = 1 := by
  sorry

end Parcours.Olymp

#verifier
