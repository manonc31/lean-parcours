/- @parcours
titre: Un petit sudoku
difficulte: 1
requiert: Enigmes.CarreMagique
indice: Case 0 : la ligne 0 contient déjà un 2, la colonne 0… commence par les cases les plus contraintes.
indice: Il y a plusieurs solutions possibles : n'importe laquelle convient !
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Un petit sudoku

Un sudoku 4 × 4 : chaque ligne, chaque colonne et chaque bloc 2 × 2 contient 1, 2, 3, 4.
La grille est lue ligne par ligne (cases 0 à 15). Les indices sont donnés sous la forme
`(case, valeur)`.

```
. 2 | . .
. . | 1 .
----+----
. 1 | . .
. . | 2 .
```

## À faire
Complète `maGrille` et prouve `maGrille_ok`.
-/

namespace Parcours.Enigmes

def groupesSudoku : List (List Nat) :=
  [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15],
   [0, 4, 8, 12], [1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15],
   [0, 1, 4, 5], [2, 3, 6, 7], [8, 9, 12, 13], [10, 11, 14, 15]]

def GrilleOk (g : List Nat) : Bool :=
  g.length == 16 && g.all (fun x => 1 ≤ x && x ≤ 4) &&
    groupesSudoku.all fun gr => (gr.map (g.getD · 0)).eraseDups.length == 4

def indicesSudoku : List (Nat × Nat) := [(1, 2), (6, 1), (9, 1), (14, 2)]

def maGrille : List Nat := -- @exo
  [1, 2, 3, 4,
   3, 4, 1, 2,
   2, 1, 4, 3,
   4, 3, 2, 1]

theorem maGrille_ok : GrilleOk maGrille && indicesSudoku.all (fun p => maGrille.getD p.1 0 == p.2) = true := by -- @exo
  decide

end Parcours.Enigmes

#verifier
