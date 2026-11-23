import Exercices.Arithmetique.Definitions

/-!
# L'identité des quatre carrés

## Se le représenter
Euler (1748) : le produit de deux sommes de **quatre** carrés est une somme de quatre carrés.
C'est l'étape clé du théorème de Lagrange (« tout entier est somme de quatre carrés ») et, vu
aujourd'hui, la multiplication des **quaternions** de Hamilton.

## À prouver
`quatre_carres` : l'identité d'Euler.

## Ressources
- [Identité des quatre carrés d'Euler (Wikipédia)](https://fr.wikipedia.org/wiki/Identit%C3%A9_des_quatre_carr%C3%A9s_d%27Euler)

---
*Exercice* `Classiques.QuatreCarres` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.QuatreCarres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

theorem quatre_carres (a b c d x y z w : Int) :
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) =
      (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
      (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
