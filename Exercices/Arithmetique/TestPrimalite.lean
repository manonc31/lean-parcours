import Exercices.Arithmetique.DiviseOrdre

/-!
# Un test de primalité prouvé

`estPremier n` teste tous les diviseurs possibles (un algorithme lent, mais correct). Prouve qu'il
répond exactement `Premier n`. En récompense : `decide` peut maintenant prouver que 97 est premier !

## À prouver
1. `estPremier_correct : estPremier n = true ↔ Premier n`
2. `premier_97 : Premier 97`

---
*Exercice* `Arithmetique.TestPrimalite` · difficulté ★★★★☆

💡 Indices : `./parcours indice Arithmetique.TestPrimalite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

def estPremier (n : Nat) : Bool := 2 ≤ n && (List.range n).all (fun d => d < 2 || n % d != 0)

theorem estPremier_correct (n : Nat) : estPremier n = true ↔ Premier n := by
  sorry

theorem premier_97 : Premier 97 := by
  sorry

end Parcours.Arith

#verifier
