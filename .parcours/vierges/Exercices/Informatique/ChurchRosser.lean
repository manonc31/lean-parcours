import Exercices.Informatique.LambdaCalcul

/-!
# 💀 Le théorème de Church-Rosser

> Si `t` se réduit en `u` et en `v`, alors `u` et `v` se réduisent en un même terme `w`.

Conséquence : le **résultat** d'un calcul ne dépend pas de l'ordre dans lequel on évalue
(la forme normale, si elle existe, est unique). Prouvé par Church et Rosser en 1936.

C'est un classique de la formalisation, et un excellent test de ta maîtrise des récurrences
sur des structures avec des indices de de Bruijn.

Boss sans solution de référence.

## À prouver
`church_rosser : ReduitEtoile t u → ReduitEtoile t v → ∃ w, ReduitEtoile u w ∧ ReduitEtoile v w`

## Ressources
- [Théorème de Church-Rosser (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Church%E2%80%93Rosser_theorem)

---
*Exercice* `Informatique.ChurchRosser` · difficulté ★★★★★

💡 Indices : `./parcours indice Informatique.ChurchRosser` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

theorem church_rosser {t u v : Terme} (h₁ : ReduitEtoile t u) (h₂ : ReduitEtoile t v) :
    ∃ w, ReduitEtoile u w ∧ ReduitEtoile v w := by
  sorry

end Parcours.Info

#verifier
