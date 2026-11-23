/- @parcours
titre: Le problème des huit reines
difficulte: 2
requiert: Programmes.Recherche
indice: Ce sont des calculs : `decide`, ou `decide +kernel` pour les plus gros (le noyau de Lean fait des milliers de calculs).
indice: Essaie `#eval placer 6 6` pour voir les 4 solutions sur un échiquier 6 × 6.
-/
import Solutions.Programmes.Definitions

/-!
# Le problème des huit reines

Placer 8 reines sur un échiquier sans qu'aucune n'en menace une autre (ni même ligne, ni même
colonne, ni même diagonale). Gauss lui-même s'y est cassé les dents ! Une solution est une liste :
la reine de la ligne `i` est dans la colonne `l[i]`.

`placer n k` construit **toutes** les façons de placer `k` reines compatibles sur les `k`
premières lignes d'un échiquier `n × n` (c'est l'algorithme de **retour sur trace** :
on ajoute une reine seulement si elle est compatible avec les précédentes).

## À prouver
1. `une_solution : [0, 4, 7, 5, 2, 6, 1, 3] ∈ placer 8 8`
2. `quatre_vingt_douze` : il y a exactement 92 solutions.
3. `trois_impossible` : aucune solution pour 3 reines.

## Ressources
- [Problème des huit dames (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_huit_dames)
-/

namespace Parcours.Prog

def compatible (p : List Nat) (c : Nat) : Bool :=
  (List.range p.length).all fun i =>
    p.getD i 0 != c && i + c != p.length + p.getD i 0 && i + p.getD i 0 != p.length + c

def placer (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (placer n k).flatMap fun p =>
      ((List.range n).filter fun c => compatible p c).map fun c => p ++ [c]

theorem une_solution : [0, 4, 7, 5, 2, 6, 1, 3] ∈ placer 8 8 := by -- @exo
  decide +kernel

theorem quatre_vingt_douze : (placer 8 8).length = 92 := by -- @exo
  decide +kernel

theorem trois_impossible : placer 3 3 = [] := by -- @exo
  decide

end Parcours.Prog

#verifier
