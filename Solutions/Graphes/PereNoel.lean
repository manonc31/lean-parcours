/- @parcours
titre: La maison du père Noël
difficulte: 1
requiert: Graphes.Konigsberg
indice: Pars du coin 0 et essaie de garder le toit pour le milieu du dessin.
indice: `impairs` et `compte` sont des calculs.
-/
import Solutions.Graphes.Definitions

/-!
# La maison du père Noël

Le jeu d'enfant : dessiner la « maison du père Noël » (un carré avec ses deux diagonales et un
toit) **sans lever le crayon** et sans repasser sur un trait.

```
      4
     / \
    3---2
    |\ /|
    | X |
    |/ \|
    0---1
```
D'après Euler, c'est possible seulement en partant d'un sommet de degré **impair** : ici les deux
coins du bas, 0 et 1.

## À faire
1. Écris `dessin` (la suite des sommets visités) et prouve `dessin_ok`.
2. `impairs` : les sommets de degré impair sont exactement 0 et 1.
3. `compte` : il y a 44 dessins qui partent du coin 0, et aucun qui part du toit.

## Ressources
- [Das Haus vom Nikolaus (Wikipédia, en allemand)](https://de.wikipedia.org/wiki/Haus_vom_Nikolaus)
-/

namespace Parcours.Graphes

def maison : Graphe := [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3), (2, 4), (3, 4)]

def norme (e : Nat × Nat) : Nat × Nat := (min e.1 e.2, max e.1 e.2)

def traits : List Nat → List (Nat × Nat)
  | a :: b :: r => (a, b) :: traits (b :: r)
  | _ => []

def DessinOk (g : Graphe) (d : List Nat) : Bool := ((traits d).map norme).isPerm (g.map norme)

def dessin : List Nat := -- @exo
  [0, 1, 3, 4, 2, 3, 0, 2, 1]

theorem dessin_ok : DessinOk maison dessin = true := by -- @exo
  decide

theorem impairs : (List.range 5).filter (fun v => degre maison v % 2 == 1) = [0, 1] := by -- @exo
  decide

/-- Le nombre de dessins qui partent de `v` en utilisant toutes les arêtes de `g` (`f` : réserve de calcul). -/
def nbDessins : Nat → Graphe → Nat → Nat
  | _, [], _ => 1
  | 0, _, _ => 0
  | f + 1, g, v => ((List.range g.length).map fun i =>
      let e := g.getD i (0, 0)
      if e.1 == v then nbDessins f (g.eraseIdx i) e.2
      else if e.2 == v then nbDessins f (g.eraseIdx i) e.1
      else 0).sum

theorem compte : nbDessins 8 maison 0 = 44 ∧ nbDessins 8 maison 4 = 0 := by -- @exo
  decide +kernel

end Parcours.Graphes

#verifier
