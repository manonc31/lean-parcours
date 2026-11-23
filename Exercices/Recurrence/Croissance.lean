import Exercices.Recurrence.Definitions

/-!
# Qui grandit le plus vite ?

`n < 2ⁿ ≤ (n+1)! ≤ (n+1)ⁿ⁺¹`… les fonctions polynomiales, exponentielles et factorielles
n'ont pas la même vitesse. C'est le cœur de la **complexité** des algorithmes.

## À prouver
1. `lt_deux_pow (n : Nat) : n < 2 ^ n`
2. `deux_pow_le_fact (n : Nat) : 2 ^ n ≤ fact (n + 1)`
3. `fact_le_pow (n : Nat) : fact n ≤ n ^ n`

---
*Exercice* `Recurrence.Croissance` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.Croissance` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem lt_deux_pow (n : Nat) : n < 2 ^ n := by
  sorry

theorem deux_pow_le_fact (n : Nat) : 2 ^ n ≤ fact (n + 1) := by
  sorry

theorem fact_le_pow (n : Nat) : fact n ≤ n ^ n := by
  sorry

end Parcours.Recurrence

#verifier
