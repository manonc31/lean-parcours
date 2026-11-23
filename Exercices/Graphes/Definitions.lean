import Exercices.Recurrence.Definitions
import Exercices.Listes.Pont

/-!
# Les graphes (cours)

Un **graphe** est un ensemble de sommets reliés par des arêtes. Ici, les sommets sont des entiers,
et un graphe est simplement la **liste de ses arêtes** `(u, v)` (non orientées ; une arête peut
apparaître plusieurs fois, comme deux ponts entre les mêmes rives).

Le **degré** d'un sommet `v` est le nombre d'extrémités d'arêtes égales à `v`
(une boucle `(v, v)` compte deux fois).

## Ressources
- [Théorie des graphes (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9orie_des_graphes)

---
*Exercice* `Graphes.Definitions` · difficulté ★☆☆☆☆
-/

namespace Parcours.Graphes

/-- Un (multi)graphe non orienté : la liste de ses arêtes. -/
abbrev Graphe := List (Nat × Nat)

/-- Toutes les extrémités des arêtes, avec répétitions. -/
def extremites (g : Graphe) : List Nat := g.flatMap (fun e => [e.1, e.2])

def degre (g : Graphe) (v : Nat) : Nat := (extremites g).count v

theorem extremites_cons (e : Nat × Nat) (g : Graphe) :
    extremites (e :: g) = e.1 :: e.2 :: extremites g := rfl

end Parcours.Graphes
