import Exercices.Combinatoire.Definitions

/-!
# Premières valeurs du triangle

## À prouver
1. `binom_eq_zero : n < k → binom n k = 0`
2. `binom_self (n : Nat) : binom n n = 1`
3. `binom_un (n : Nat) : binom n 1 = n`

---
*Exercice* `Combinatoire.BinomBase` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Combinatoire.BinomBase` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem binom_eq_zero {n k : Nat} (h : n < k) : binom n k = 0 := by
  sorry

theorem binom_self (n : Nat) : binom n n = 1 := by
  sorry

theorem binom_un (n : Nat) : binom n 1 = n := by
  sorry

end Parcours.Combi

#verifier
