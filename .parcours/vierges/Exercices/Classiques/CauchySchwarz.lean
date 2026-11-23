import Exercices.Arithmetique.Definitions

/-!
# L'inégalité de Cauchy-Schwarz

## Se le représenter
Pour deux vecteurs `(a, b)` et `(c, d)` du plan, le produit scalaire est plus petit que le produit des
longueurs : `(ac + bd)² ≤ (a² + b²)(c² + d²)`. L'identité de Lagrange explique tout :
la différence vaut exactement `(ad − bc)²`, un carré, donc positive.

## À prouver
`carre_positif (x : Int) : 0 ≤ x * x`, puis `cauchy_schwarz (a b c d : Int) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)`

## Ressources
- [Inégalité de Cauchy-Schwarz (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_de_Cauchy-Schwarz)

---
*Exercice* `Classiques.CauchySchwarz` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Classiques.CauchySchwarz` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem carre_positif (x : Int) : 0 ≤ x * x := by
  sorry

theorem cauchy_schwarz (a b c d : Int) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  sorry

end Parcours.Classiques

#verifier
