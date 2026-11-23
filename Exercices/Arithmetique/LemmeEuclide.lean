import Exercices.Arithmetique.LemmeGauss

/-!
# Le lemme d'Euclide

> Si un nombre premier divise un produit, il divise l'un des facteurs.

C'est la propriété fondamentale des nombres premiers (Euclide, *Éléments*, livre VII, ~300 av. J.-C.).

## À prouver
`premier_divise_mul : Premier p → p ∣ a * b → p ∣ a ∨ p ∣ b`

## Ressources
- [Lemme d'Euclide (Wikipédia)](https://fr.wikipedia.org/wiki/Lemme_d%27Euclide)

---
*Exercice* `Arithmetique.LemmeEuclide` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.LemmeEuclide` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem premier_divise_mul {p a b : Nat} (hp : Premier p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  sorry

end Parcours.Arith

#verifier
