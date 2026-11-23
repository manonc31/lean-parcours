import Exercices.Graphes.Definitions

/-!
# Le lemme des poignées de main

Dans une soirée, si on additionne pour chaque invité le nombre de mains qu'il a serrées, on
obtient un nombre **pair** : chaque poignée de main est comptée deux fois.
En graphes : la somme des degrés vaut deux fois le nombre d'arêtes (Euler, 1736).

## À prouver
1. `longueur_extremites : (extremites g).length = 2 * g.length`
2. `poignees_de_mains : (∀ e ∈ g, e.1 < n ∧ e.2 < n) → ((List.range n).map (degre g)).sum = 2 * g.length`

## Ressources
- [Lemme des poignées de main (Wikipédia)](https://fr.wikipedia.org/wiki/Lemme_des_poign%C3%A9es_de_main)

---
*Exercice* `Graphes.PoigneesDeMains` · difficulté ★★★★☆

💡 Indices : `./parcours indice Graphes.PoigneesDeMains` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Graphes

theorem longueur_extremites (g : Graphe) : (extremites g).length = 2 * g.length := by
  sorry

theorem poignees_de_mains (g : Graphe) (n : Nat) (h : ∀ e ∈ g, e.1 < n ∧ e.2 < n) :
    ((List.range n).map (degre g)).sum = 2 * g.length := by
  sorry

end Parcours.Graphes

#verifier
