/- @parcours
titre: Le nombre cyclique 142857
difficulte: 1
requiert: Enigmes.Nombre1089
indice: `decide` sait vérifier un `∃ r, r < 6 ∧ …` (il essaie les 6 valeurs).
-/
import Solutions.Recurrence.Definitions

/-!
# Le nombre cyclique 142857

`142857 × 2 = 285714`, `× 3 = 428571`, `× 4 = 571428`, `× 5 = 714285`, `× 6 = 857142` : toujours
les mêmes chiffres, qui **tournent** ! Et `142857 × 7 = 999999`. Le secret : `1/7 = 0,142857142857…`

## À prouver
1. `rotations` : pour `k` de 1 à 6, les chiffres de `142857 × k` sont une rotation de ceux de 142857.
2. `fois_sept : 142857 * 7 = 999999`
-/

namespace Parcours.Enigmes

def chiffres6 (n : Nat) : List Nat :=
  [n / 100000 % 10, n / 10000 % 10, n / 1000 % 10, n / 100 % 10, n / 10 % 10, n % 10]

theorem rotations : ∀ k, k < 6 → ∃ r, r < 6 ∧ chiffres6 (142857 * (k + 1)) = (chiffres6 142857).rotateLeft r := by -- @exo
  decide

theorem fois_sept : 142857 * 7 = 999999 := by -- @exo
  decide

end Parcours.Enigmes

#verifier
