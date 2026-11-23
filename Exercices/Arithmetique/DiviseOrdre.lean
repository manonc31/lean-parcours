import Exercices.Arithmetique.DiviseBase

/-!
# Divisibilité et ordre

Un diviseur d'un nombre non nul est plus petit que lui. Et la divisibilité est une
relation d'ordre (antisymétrique !) sur les entiers naturels.

## À prouver
1. `divise_le : a ∣ b → 0 < b → a ≤ b`
2. `divise_antisymm : a ∣ b → b ∣ a → a = b`
3. `divise_un : a ∣ 1 → a = 1`

---
*Exercice* `Arithmetique.DiviseOrdre` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Arithmetique.DiviseOrdre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem divise_le {a b : Nat} (h : a ∣ b) (hb : 0 < b) : a ≤ b := by
  sorry

theorem divise_antisymm {a b : Nat} (h1 : a ∣ b) (h2 : b ∣ a) : a = b := by
  sorry

theorem divise_un {a : Nat} (h : a ∣ 1) : a = 1 := by
  sorry

end Parcours.Arith

#verifier
