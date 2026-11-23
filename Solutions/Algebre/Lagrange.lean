/- @parcours
celebre: 71
titre: Le théorème de Lagrange
difficulte: 5
genre: boss
solution: non
requiert: Algebre.Noyau, Combinatoire.Tiroirs
indice: Les classes `g * H = {g * h | h ∈ H}` forment une partition de `G` : deux classes sont égales ou disjointes.
indice: Chaque classe a autant d'éléments que `H` (la multiplication à gauche par `g` est une bijection).
indice: Donc `|G| = (nombre de classes) × |H|`. Formaliser les « classes » avec des listes est le vrai travail : récurrence sur la liste des éléments pas encore couverts.
-/
import Solutions.Algebre.SousGroupes
import Solutions.Combinatoire.Tiroirs

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
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem lagrange (H : SousGroupe G) [DecidablePred H.mem] (l : List G) (hl : l.Nodup)
    (hall : ∀ g, g ∈ l) : (l.filter (fun g => decide (H.mem g))).length ∣ l.length := by -- @exo
  sorry

end Parcours.Algebre

#verifier
