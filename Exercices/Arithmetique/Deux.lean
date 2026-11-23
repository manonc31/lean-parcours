import Exercices.Arithmetique.DiviseOrdre

/-!
# Le premier des premiers

`2` est premier, et c'est le seul premier pair.

## À prouver
1. `premier_deux : Premier 2`
2. `premier_impair : Premier p → p ≠ 2 → p % 2 = 1`

---
*Exercice* `Arithmetique.Deux` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Arithmetique.Deux` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem premier_deux : Premier 2 := by
  sorry

theorem premier_impair {p : Nat} (hp : Premier p) (h2 : p ≠ 2) : p % 2 = 1 := by
  sorry

end Parcours.Arith

#verifier
