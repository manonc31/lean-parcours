/- @parcours
titre: Le voyageur de commerce
difficulte: 2
requiert: Combinatoire.Anagrammes
indice: Commence par les petites distances : 0 → 1 coûte 2, 1 → 3 coûte 4…
indice: `perms` vient de l'exercice « Les anagrammes ».
-/
import Solutions.Programmes.Definitions
import Solutions.Combinatoire.Anagrammes

/-!
# Le voyageur de commerce

Un voyageur part de la ville 0, doit visiter les villes 1, 2, 3, 4 et revenir. Quel est le plus
court circuit ? Avec 5 villes, on peut tout essayer (24 ordres) ; avec 30 villes, il y aurait plus
de circuits que d'atomes dans l'univers. Ce problème est **NP-difficile** : on ne connaît aucun
algorithme rapide, et il y a un million de dollars à gagner (problème P = NP) pour qui en trouve un
ou prouve qu'il n'en existe pas.

## À faire
Trouve `meilleurTour` (l'ordre de visite des villes 1 à 4) et prouve `optimal`.

## Ressources
- [Problème du voyageur de commerce (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_voyageur_de_commerce)
-/

namespace Parcours.Prog

open Parcours.Combi

def distances : List (List Nat) :=
  [[0, 2, 9, 10, 7], [2, 0, 6, 4, 3], [9, 6, 0, 8, 5], [10, 4, 8, 0, 6], [7, 3, 5, 6, 0]]

def dist (a b : Nat) : Nat := (distances.getD a []).getD b 0

def longueurTour (t : List Nat) : Nat := (((0 :: t).zip (t ++ [0])).map fun p => dist p.1 p.2).sum

def meilleurTour : List Nat := -- @exo
  [1, 3, 2, 4]

theorem optimal : meilleurTour.isPerm [1, 2, 3, 4] = true ∧ longueurTour meilleurTour = 26 ∧
    ∀ t ∈ perms [1, 2, 3, 4], 26 ≤ longueurTour t := by -- @exo
  decide

end Parcours.Prog

#verifier
