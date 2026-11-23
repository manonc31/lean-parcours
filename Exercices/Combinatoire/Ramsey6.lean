import Exercices.Combinatoire.Definitions

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

---
*Exercice* `Combinatoire.Ramsey6` · difficulté ★★★★★

💡 Indices : `./parcours indice Combinatoire.Ramsey6` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem ramsey_six (c : Fin 6 → Fin 6 → Bool) (hc : ∀ i j, c i j = c j i) :
    ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ c i j = c j k ∧ c j k = c i k := by
  sorry

end Parcours.Combi

#verifier
