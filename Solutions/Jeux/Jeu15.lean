/- @parcours
titre: Le jeu de 15
difficulte: 1
requiert: Enigmes.CarreMagique
indice: Tout se vérifie par le calcul : `decide`.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Le jeu de 15

Deux joueurs choisissent à tour de rôle un nombre de 1 à 9 (chacun une seule fois). Le premier
qui possède **trois nombres dont la somme fait 15** a gagné. Ce jeu semble difficile… mais c'est un
**morpion déguisé** ! Dans le carré magique de Lo Shu, les triplets de somme 15 sont exactement les
8 lignes, colonnes et diagonales.
```
2 7 6
9 5 1
4 3 8
```

## À prouver
1. `huit_triplets` : il y a exactement 8 triplets de nombres distincts de 1 à 9 de somme 15.
2. `morpion` : chacun est une ligne du carré magique (et réciproquement).

## Ressources
- [Isomorphisme du jeu de 15 et du morpion (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Number_Scrabble)
-/

namespace Parcours.Jeux

def triplets15 : List (List Nat) :=
  (List.range 10).flatMap fun a => (List.range 10).flatMap fun b => (List.range 10).filterMap fun c =>
    if 0 < a ∧ a < b ∧ b < c ∧ a + b + c = 15 then some [a, b, c] else none

def loShu : List Nat := [2, 7, 6, 9, 5, 1, 4, 3, 8]

def lignesMorpion : List (List Nat) :=
  [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]]

def lignesLoShu : List (List Nat) := lignesMorpion.map fun l => l.map (loShu.getD · 0)

theorem huit_triplets : triplets15.length = 8 := by -- @exo
  decide

theorem morpion : (∀ t ∈ triplets15, ∃ l ∈ lignesLoShu, t.isPerm l = true) ∧
    (∀ l ∈ lignesLoShu, ∃ t ∈ triplets15, t.isPerm l = true) := by -- @exo
  decide

end Parcours.Jeux

#verifier
