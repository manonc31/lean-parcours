import Exercices.Arithmetique.Definitions

/-!
# Le produit de deux sommes de deux carrés

## Se le représenter
`5 = 1² + 2²` et `13 = 2² + 3²`, alors `65 = 5 × 13` est aussi une somme de deux carrés :
`65 = 4² + 7² = 1² + 8²`. C'est toujours vrai, grâce à l'identité de Brahmagupta (VIIᵉ siècle) :
c'est la multiplication des nombres complexes `|z|² |w|² = |zw|²` !

## À prouver
1. `brahmagupta : (a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²`
2. `soixante_cinq : 65 = 4 ^ 2 + 7 ^ 2 ∧ 65 = 1 ^ 2 + 8 ^ 2`

## Ressources
- [Identité de Brahmagupta (Wikipédia)](https://fr.wikipedia.org/wiki/Identit%C3%A9_de_Brahmagupta)

---
*Exercice* `Classiques.Brahmagupta` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.Brahmagupta` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

theorem brahmagupta (a b c d : Int) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  sorry

theorem soixante_cinq : (65 : Nat) = 4 ^ 2 + 7 ^ 2 ∧ (65 : Nat) = 1 ^ 2 + 8 ^ 2 := by
  sorry

end Parcours.Classiques

#verifier
