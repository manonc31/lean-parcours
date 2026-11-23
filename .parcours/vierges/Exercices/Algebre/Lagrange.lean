import Exercices.Algebre.SousGroupes
import Exercices.Combinatoire.Tiroirs

/-!
# 💀 Le théorème de Lagrange

> Dans un groupe fini, le nombre d'éléments d'un sous-groupe **divise** le nombre d'éléments du groupe.

Conséquence : un groupe à 7 éléments n'a que des sous-groupes triviaux ; l'ordre de tout
élément divise l'ordre du groupe (ce qui redonne le petit théorème de Fermat !).

On représente « `G` est fini » par une liste `l` sans doublon qui contient tous les éléments.

Boss sans solution de référence.

## À prouver
`lagrange (H : SousGroupe G) [DecidablePred H.mem] (l : List G) (hl : l.Nodup) (hall : ∀ g, g ∈ l) :
  (l.filter (fun g => decide (H.mem g))).length ∣ l.length`

## Ressources
- [Théorème de Lagrange (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Lagrange_sur_les_groupes)

---
*Exercice* `Algebre.Lagrange` · difficulté ★★★★★

💡 Indices : `./parcours indice Algebre.Lagrange` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem lagrange (H : SousGroupe G) [DecidablePred H.mem] (l : List G) (hl : l.Nodup)
    (hall : ∀ g, g ∈ l) : (l.filter (fun g => decide (H.mem g))).length ∣ l.length := by
  sorry

end Parcours.Algebre

#verifier
