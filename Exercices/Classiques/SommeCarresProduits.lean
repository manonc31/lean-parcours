import Exercices.Classiques.CauchySchwarz

/-!
# x² + y² + z² ≥ xy + yz + zx

## Se le représenter
Additionne les trois carrés `(x − y)²`, `(y − z)²`, `(z − x)²` : c'est positif, et ça vaut
`2(x² + y² + z²) − 2(xy + yz + zx)`.

## À prouver
`somme_carres_produits : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2`

---
*Exercice* `Classiques.SommeCarresProduits` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.SommeCarresProduits` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

theorem somme_carres_produits (x y z : Int) : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
