import Exercices.Programmes.Definitions
import Exercices.Combinatoire.Anagrammes

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

---
*Exercice* `Programmes.Voyageur` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Voyageur` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

open Parcours.Combi

def distances : List (List Nat) :=
  [[0, 2, 9, 10, 7], [2, 0, 6, 4, 3], [9, 6, 0, 8, 5], [10, 4, 8, 0, 6], [7, 3, 5, 6, 0]]

def dist (a b : Nat) : Nat := (distances.getD a []).getD b 0

def longueurTour (t : List Nat) : Nat := (((0 :: t).zip (t ++ [0])).map fun p => dist p.1 p.2).sum

def meilleurTour : List Nat :=
  sorry

theorem optimal : meilleurTour.isPerm [1, 2, 3, 4] = true ∧ longueurTour meilleurTour = 26 ∧
    ∀ t ∈ perms [1, 2, 3, 4], 26 ≤ longueurTour t := by
  sorry

end Parcours.Prog

#verifier
