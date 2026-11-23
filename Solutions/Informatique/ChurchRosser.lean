/- @parcours
titre: Le théorème de Church-Rosser
difficulte: 5
genre: boss
solution: non
requiert: Informatique.LambdaCalcul
indice: La méthode de Tait et Martin-Löf : définis la **réduction parallèle** `⇉` (on réduit en même temps n'importe quel ensemble de rédex). Elle vérifie `→ ⊆ ⇉ ⊆ →*`.
indice: Montre que `⇉` a la propriété du diamant. L'astuce de Takahashi : le « développement complet » `t*` (on réduit TOUS les rédex) vérifie `t ⇉ u → u ⇉ t*`.
indice: Le cœur technique : des lemmes de commutation entre `relever` et `substituer`. Prévois-en une demi-douzaine, prouvés par récurrence sur le terme en généralisant les indices.
-/
import Solutions.Informatique.LambdaCalcul

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
-/

namespace Parcours.Info

theorem church_rosser {t u v : Terme} (h₁ : ReduitEtoile t u) (h₂ : ReduitEtoile t v) :
    ∃ w, ReduitEtoile u w ∧ ReduitEtoile v w := by -- @exo
  sorry

end Parcours.Info

#verifier
