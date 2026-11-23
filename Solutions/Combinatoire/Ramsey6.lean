/- @parcours
celebre: 31
titre: Le théorème d'amitié (R(3,3) = 6)
difficulte: 5
genre: boss
solution: non
requiert: Combinatoire.Ramsey5, Combinatoire.Tiroirs
indice: Regarde la personne `0`. Parmi les 5 autres, au moins 3 ont la même relation avec elle (tiroirs : 5 personnes, 2 couleurs).
indice: Si deux de ces trois ont entre elles cette même relation, triangle avec `0`. Sinon, ces trois forment un triangle de l'autre couleur.
indice: L'astuce Lean : énumérer les cas sans tout écrire à la main. `decide` ne peut pas parcourir toutes les fonctions `c`, mais il peut vérifier des énoncés sur `Bool` à 5 variables (les couleurs `c 0 1, …, c 0 5`).
-/
import Solutions.Combinatoire.Definitions

/-!
# 💀 Le théorème d'amitié

> Dans toute soirée de **6** personnes, il y en a 3 qui se connaissent toutes,
> ou 3 qui ne se connaissent pas du tout.

C'est le plus petit cas du théorème de Ramsey : `R(3,3) = 6`. (On ne connaît toujours pas
`R(5,5)` : quelque part entre 43 et 46. Erdős disait que si des extraterrestres exigeaient
`R(5,5)` sous peine de détruire la Terre, il faudrait mobiliser tous les ordinateurs ; s'ils
demandaient `R(6,6)`, il faudrait plutôt essayer de détruire les extraterrestres.)

Boss sans solution de référence.

## À prouver
`ramsey_six (c : Fin 6 → Fin 6 → Bool) (hc : ∀ i j, c i j = c j i) :
  ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ c i j = c j k ∧ c j k = c i k`
-/

namespace Parcours.Combi

theorem ramsey_six (c : Fin 6 → Fin 6 → Bool) (hc : ∀ i j, c i j = c j i) :
    ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ c i j = c j k ∧ c j k = c i k := by -- @exo
  sorry

end Parcours.Combi

#verifier
