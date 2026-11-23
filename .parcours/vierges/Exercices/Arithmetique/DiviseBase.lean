import Exercices.Arithmetique.Definitions

/-!
# Premières propriétés de la divisibilité

## À prouver
1. `divise_refl : a ∣ a`
2. `divise_zero : a ∣ 0`
3. `un_divise : 1 ∣ a`
4. `divise_trans : a ∣ b → b ∣ c → a ∣ c`
5. `divise_add : a ∣ b → a ∣ c → a ∣ b + c`
6. `divise_mul_droite : a ∣ b → a ∣ b * c`
7. `divise_mul_gauche : a ∣ b * a`
8. `divise_sub : a ∣ b + c → a ∣ b → a ∣ c`

---
*Exercice* `Arithmetique.DiviseBase` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Arithmetique.DiviseBase` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem divise_refl (a : Nat) : a ∣ a := by
  sorry

theorem divise_zero (a : Nat) : a ∣ 0 := by
  sorry

theorem un_divise (a : Nat) : 1 ∣ a := by
  sorry

theorem divise_trans {a b c : Nat} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  sorry

theorem divise_add {a b c : Nat} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  sorry

theorem divise_mul_droite {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ b * c := by
  sorry

theorem divise_mul_gauche (a b : Nat) : a ∣ b * a := by
  sorry

theorem divise_sub {a b c : Nat} (h1 : a ∣ b + c) (h2 : a ∣ b) : a ∣ c := by
  sorry

end Parcours.Arith

#verifier
