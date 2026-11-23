import Exercices.Constructions.OperationsZ

/-!
# ℤ est un anneau commutatif

Tu as construit `Zr`. Vérifions que c'est bien « les entiers relatifs » : toutes les règles de
calcul sont vraies. La méthode est toujours la même : se ramener à des couples, puis à une
égalité dans `Nat`.

## À prouver
1. `add_comm`, `add_assoc`, `zero_add`, `add_neg` (`x + -x = 0` : **la** nouveauté par rapport à ℕ !)
2. `mul_comm`, `mul_assoc`, `one_mul`, `mul_add`

---
*Exercice* `Constructions.AnneauZ` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Constructions.AnneauZ` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions.Zr

theorem add_comm (x y : Zr) : x + y = y + x := by
  sorry

theorem add_assoc (x y z : Zr) : x + y + z = x + (y + z) := by
  sorry

theorem zero_add (x : Zr) : 0 + x = x := by
  sorry

theorem add_neg (x : Zr) : x + -x = 0 := by
  sorry

theorem mul_comm (x y : Zr) : x * y = y * x := by
  sorry

theorem mul_assoc (x y z : Zr) : x * y * z = x * (y * z) := by
  sorry

theorem one_mul (x : Zr) : 1 * x = x := by
  sorry

theorem mul_add (x y z : Zr) : x * (y + z) = x * y + x * z := by
  sorry

end Parcours.Constructions.Zr

#verifier
