import Exercices.Classiques.CauchySchwarz

/-!
# a³ + b³ ≥ a²b + ab²

## Se le représenter
Pour `a, b ≥ 0` : `a³ + b³ − a²b − ab² = (a + b)(a − b)²`, produit de deux nombres positifs.

## À prouver
`cubes_produits : 0 ≤ a → 0 ≤ b → a ^ 2 * b + a * b ^ 2 ≤ a ^ 3 + b ^ 3`

---
*Exercice* `Classiques.CubesProduits` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.CubesProduits` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

theorem cubes_produits (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * b + a * b ^ 2 ≤ a ^ 3 + b ^ 3 := by
  sorry

end Parcours.Classiques

#verifier
