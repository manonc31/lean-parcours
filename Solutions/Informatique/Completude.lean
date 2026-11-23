/- @parcours
titre: Le théorème de complétude
difficulte: 5
genre: boss
solution: non
requiert: Informatique.LogiqueProp
indice: Étape 1 : le théorème de la déduction (si `a` permet de prouver `b`, alors `a → b` est prouvable). Il faut d'abord définir « prouvable à partir d'hypothèses ».
indice: Étape 2 (lemme de Kalmár) : pour une valuation `v`, notons `aᵛ` = `a` si `v a = vrai`, `a → faux` sinon. Alors à partir des `xᵢᵛ`, on prouve `fᵛ`. Récurrence sur `f`.
indice: Étape 3 : éliminer les hypothèses une par une, en combinant les cas `xᵢ` et `¬xᵢ`.
-/
import Solutions.Informatique.LogiqueProp

/-!
# 💀 Le théorème de complétude

La réciproque de la correction : **toute tautologie est prouvable** dans le système à la Hilbert.
Avec la correction, cela dit que « vrai » et « prouvable » coïncident en logique propositionnelle.
(Gödel montrera que c'est encore vrai en logique du premier ordre… mais pas pour l'arithmétique !)

Boss sans solution de référence.

## À prouver
`completude (f : Formule) (h : ∀ v, f.eval v = true) : Prouvable f`

## Ressources
- [Théorème de complétude (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_compl%C3%A9tude_de_G%C3%B6del)
-/

namespace Parcours.Info

theorem completude (f : Formule) (h : ∀ v, f.eval v = true) : Prouvable f := by -- @exo
  sorry

end Parcours.Info

#verifier
