import Exercices.Programmes.Definitions

/-!
# Est-ce une puissance de 2 ?

Pour tester si `n` est une puissance de 2 : on divise par 2 tant que c'est pair, et on regarde
si on arrive à 1.

## À prouver
1. `puissance_ok : estPuissance2 (2 ^ k) = true`
2. `puissance_correct : estPuissance2 n = true → ∃ k, n = 2 ^ k`

---
*Exercice* `Programmes.PuissanceDeux` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.PuissanceDeux` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def estPuissance2 (n : Nat) : Bool :=
  if n ≤ 1 then n == 1 else n % 2 == 0 && estPuissance2 (n / 2)
termination_by n
decreasing_by omega

theorem puissance_ok (k : Nat) : estPuissance2 (2 ^ k) = true := by
  sorry

theorem puissance_correct (n : Nat) (h : estPuissance2 n = true) : ∃ k, n = 2 ^ k := by
  sorry

end Parcours.Prog

#verifier
