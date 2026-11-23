/- @parcours
titre: Les nombres heureux
difficulte: 1
requiert: Programmes.RegarderDire
indice: Des calculs : `decide` / `decide +kernel`.
indice: Pour comprendre `toujours` : pour un nombre à 4 chiffres, la somme des carrés des chiffres est au plus `4 × 81 = 324` ; tout finit par descendre sous 1000.
-/
import Solutions.Programmes.Definitions

/-!
# Les nombres heureux

Prends un nombre, remplace-le par la somme des carrés de ses chiffres, et recommence :
`7 → 49 → 97 → 130 → 10 → 1`. Si on arrive à 1, le nombre est **heureux**. Sinon, on tombe
toujours dans le même cycle : `4 → 16 → 37 → 58 → 89 → 145 → 42 → 20 → 4`.

## À prouver
1. `sept_heureux : repeter carresChiffres 5 7 = 1`
2. `cycle_malheureux : repeter carresChiffres 8 4 = 4`
3. `dix_neuf` : il y a 19 nombres heureux entre 1 et 99.
4. `toujours` : pour tout `0 < n < 1000`, après 20 étapes on est à 1 ou dans le cycle de 4.

## Ressources
- [Nombre heureux (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_heureux)
-/

namespace Parcours.Prog

def carresChiffres (n : Nat) : Nat :=
  (n % 10) ^ 2 + (n / 10 % 10) ^ 2 + (n / 100 % 10) ^ 2 + (n / 1000 % 10) ^ 2

def cycle4 : List Nat := [4, 16, 37, 58, 89, 145, 42, 20]

theorem sept_heureux : repeter carresChiffres 5 7 = 1 := by -- @exo
  decide

theorem cycle_malheureux : repeter carresChiffres 8 4 = 4 := by -- @exo
  decide

theorem dix_neuf : ((List.range 100).filter fun n => 0 < n && repeter carresChiffres 20 n == 1).length = 19 := by -- @exo
  decide +kernel

theorem toujours : ∀ n, n < 1000 → 0 < n → repeter carresChiffres 20 n = 1 ∨ repeter carresChiffres 20 n ∈ cycle4 := by -- @exo
  decide +kernel

end Parcours.Prog

#verifier
