/- @parcours
titre: Sortir du labyrinthe
difficulte: 2
requiert: Programmes.Reines
indice: Descends d'abord le long du bord gauche.
indice: `plus_court` est un calcul : `decide`.
-/
import Solutions.Programmes.Definitions

/-!
# Sortir du labyrinthe

Le parcours **en largeur** trouve le plus court chemin dans un labyrinthe : on explore d'abord
toutes les cases à distance 1, puis 2, etc. (comme une tache d'encre qui s'étale).
```
S . # . .
. # # . #
. . . # .
# . # . .
. . . . E
```
Les cases sont numérotées `5 × ligne + colonne` ; `S` = 0, `E` = 24.

## À faire
1. Écris `cheminSortie` (la suite des cases, de 0 à 24) et prouve `chemin_ok`.
2. `plus_court` : le parcours en largeur trouve 8, donc ton chemin (8 pas) est optimal.

## Ressources
- [Algorithme de parcours en largeur (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_parcours_en_largeur)
-/

namespace Parcours.Prog

def murs : List Bool :=
  [false, false, true, false, false,
   false, true, true, false, true,
   false, false, false, true, false,
   true, false, true, false, false,
   false, false, false, false, false]

def libre (p : Nat) : Bool := p < 25 && !murs.getD p true

def voisinsL (p : Nat) : List Nat :=
  ((if p % 5 = 0 then [] else [p - 1]) ++ (if p % 5 = 4 then [] else [p + 1]) ++
    (if p < 5 then [] else [p - 5]) ++ [p + 5]).filter libre

def cheminOk : List Nat → Bool
  | a :: b :: r => (voisinsL a).contains b && cheminOk (b :: r)
  | _ => true

/-- Parcours en largeur : distance de la sortie (`f` : réserve). -/
def distance : Nat → List Nat → List Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | f + 1, vus, front, d =>
    if front.contains 24 then some d
    else
      let nouveaux := ((front.flatMap voisinsL).eraseDups).filter (fun p => !vus.contains p)
      if nouveaux.isEmpty then none else distance f (vus ++ nouveaux) nouveaux (d + 1)

def cheminSortie : List Nat := -- @exo
  [0, 5, 10, 11, 16, 21, 22, 23, 24]

theorem chemin_ok : cheminSortie.head? = some 0 ∧ cheminSortie.getLast? = some 24 ∧
    cheminOk cheminSortie = true ∧ cheminSortie.length = 9 := by -- @exo
  decide

theorem plus_court : distance 30 [0] [0] 0 = some 8 := by -- @exo
  decide

end Parcours.Prog

#verifier
