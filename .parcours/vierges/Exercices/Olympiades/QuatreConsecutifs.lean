import Exercices.Arithmetique.Definitions

/-!
# Quatre entiers consécutifs

> Le produit de quatre entiers consécutifs, plus 1, est toujours un carré parfait.

`1·2·3·4 + 1 = 25`, `2·3·4·5 + 1 = 121`, `3·4·5·6 + 1 = 361`… Lequel ? `(n² + 3n + 1)²`.

## À prouver
`quatre_consecutifs : n * (n + 1) * (n + 2) * (n + 3) + 1 = (n * n + 3 * n + 1) ^ 2`

---
*Exercice* `Olympiades.QuatreConsecutifs` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.QuatreConsecutifs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem quatre_consecutifs (n : Nat) :
    n * (n + 1) * (n + 2) * (n + 3) + 1 = (n * n + 3 * n + 1) ^ 2 := by
  sorry

end Parcours.Olymp

#verifier
