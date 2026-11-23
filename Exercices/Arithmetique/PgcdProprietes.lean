import Exercices.Arithmetique.PgcdDivise
import Exercices.Arithmetique.DiviseOrdre

/-!
# Propriétés du PGCD

Le PGCD est **symétrique** (même si l'algorithme d'Euclide ne l'est pas !).

## À prouver
1. `pgcd_comm : pgcd a b = pgcd b a`
2. `pgcd_zero_gauche : pgcd 0 a = a`
3. `pgcd_un : pgcd 1 a = 1`

---
*Exercice* `Arithmetique.PgcdProprietes` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.PgcdProprietes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem pgcd_comm (a b : Nat) : pgcd a b = pgcd b a := by
  sorry

theorem pgcd_zero_gauche (a : Nat) : pgcd 0 a = a := by
  sorry

theorem pgcd_un (a : Nat) : pgcd 1 a = 1 := by
  sorry

end Parcours.Arith

#verifier
