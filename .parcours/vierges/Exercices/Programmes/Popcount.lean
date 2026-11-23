import Exercices.Programmes.Definitions

/-!
# Compter les bits à 1

Combien de `1` dans l'écriture binaire de `n` ? (Les processeurs ont une instruction exprès,
`popcount`.) On regarde le dernier bit (`n % 2`) et on recommence avec `n / 2`.

## À prouver
1. `bits1_double : bits1 (2 * n) = bits1 n` et `bits1_double_un : bits1 (2 * n + 1) = bits1 n + 1`
2. `bits1_puissance : bits1 (2 ^ k) = 1` (`100…0`)
3. `bits1_mersenne : bits1 (2 ^ k - 1) = k` (`11…1`)

---
*Exercice* `Programmes.Popcount` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Popcount` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def bits1 (n : Nat) : Nat := if n = 0 then 0 else n % 2 + bits1 (n / 2)
termination_by n
decreasing_by omega

theorem bits1_zero : bits1 0 = 0 := by
  sorry

theorem bits1_double (n : Nat) : bits1 (2 * n) = bits1 n := by
  sorry

theorem bits1_double_un (n : Nat) : bits1 (2 * n + 1) = bits1 n + 1 := by
  sorry

theorem bits1_puissance (k : Nat) : bits1 (2 ^ k) = 1 := by
  sorry

theorem bits1_mersenne (k : Nat) : bits1 (2 ^ k - 1) = k := by
  sorry

end Parcours.Prog

#verifier
