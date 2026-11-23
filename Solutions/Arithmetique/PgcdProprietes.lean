/- @parcours
titre: Propriétés du PGCD
difficulte: 3
requiert: Arithmetique.PgcdDivise
indice: `pgcd_comm` : deux nombres qui se divisent mutuellement sont égaux (`divise_antisymm`). Chaque PGCD divise l'autre, grâce à `divise_pgcd` et `pgcd_divise`.
-/
import Solutions.Arithmetique.PgcdDivise
import Solutions.Arithmetique.DiviseOrdre

/-!
# Propriétés du PGCD

Le PGCD est **symétrique** (même si l'algorithme d'Euclide ne l'est pas !).

## À prouver
1. `pgcd_comm : pgcd a b = pgcd b a`
2. `pgcd_zero_gauche : pgcd 0 a = a`
3. `pgcd_un : pgcd 1 a = 1`
-/

namespace Parcours.Arith

theorem pgcd_comm (a b : Nat) : pgcd a b = pgcd b a := by -- @exo
  apply divise_antisymm
  · exact divise_pgcd (pgcd_divise a b).2 (pgcd_divise a b).1
  · exact divise_pgcd (pgcd_divise b a).2 (pgcd_divise b a).1

theorem pgcd_zero_gauche (a : Nat) : pgcd 0 a = a := by -- @exo
  rw [pgcd_comm, pgcd_zero]

theorem pgcd_un (a : Nat) : pgcd 1 a = 1 := by -- @exo
  exact divise_un (pgcd_divise 1 a).1

end Parcours.Arith

#verifier
