/- @parcours
titre: Les zéros de 100!
difficulte: 1
requiert: Recurrence.SommeFactorielles
indice: `decide` calcule même `100!`.
-/
import Solutions.Recurrence.Definitions

/-!
# Les zéros de 100!

## Se le représenter
Par combien de zéros se termine `100! = 1 × 2 × ⋯ × 100` (un nombre de 158 chiffres) ? Chaque zéro
vient d'un facteur `10 = 2 × 5`, et il y a bien plus de 2 que de 5. On compte donc les 5 : les
multiples de 5 en apportent un (20 nombres), les multiples de 25 un second (4 nombres) : **24**
zéros (formule de Legendre).

## À prouver
1. `legendre : 100 / 5 + 100 / 25 = 24`
2. `vingt_quatre` : `100!` est divisible par `10²⁴` mais pas par `10²⁵`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem legendre : 100 / 5 + 100 / 25 = 24 := by -- @exo
  decide

theorem vingt_quatre : fact 100 % 10 ^ 24 = 0 ∧ fact 100 % 10 ^ 25 ≠ 0 := by -- @exo
  decide

end Parcours.Classiques

#verifier
