/- @parcours
titre: Un sudoku à solution unique
difficulte: 2
requiert: Enigmes.Sudoku
indice: Un calcul : `decide +kernel` fait tourner le solveur.
indice: Essaie `#eval resoudre 16 [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 2, 0]` : la grille de l'exercice « Un petit sudoku » a 4 solutions !
-/
import Solutions.Enigmes.Sudoku

/-!
# Un sudoku à solution unique

Un bon sudoku n'a qu'**une** solution. Celui-ci n'a que 4 indices, et pourtant sa solution est
unique ! On le prouve avec un **solveur** par retour sur trace : on remplit la première case vide
avec chaque valeur compatible, et on continue récursivement.
```
. . | . 4
3 . | . .
----+----
2 . | . .
. . | . 1
```

## À prouver
`unique_solution : resoudre 16 grilleDure = [ … la solution … ]`
-/

namespace Parcours.Enigmes

def compatibleS (g : List Nat) (i v : Nat) : Bool :=
  groupesSudoku.all fun gr => !(gr.contains i) || gr.all fun j => g.getD j 0 != v

def resoudre : Nat → List Nat → List (List Nat)
  | 0, g => if g.contains 0 then [] else [g]
  | f + 1, g =>
    match g.findIdx? (· == 0) with
    | none => [g]
    | some i => ([1, 2, 3, 4].filter (compatibleS g i)).flatMap fun v => resoudre f (g.set i v)

def grilleDure : List Nat := [0, 0, 0, 4, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1]

theorem unique_solution :
    resoudre 16 grilleDure = [[1, 2, 3, 4, 3, 4, 1, 2, 2, 1, 4, 3, 4, 3, 2, 1]] := by -- @exo
  decide +kernel

end Parcours.Enigmes

#verifier
