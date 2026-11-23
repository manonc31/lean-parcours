import Exercices.Arithmetique.Definitions

/-!
# Les congruences

`a ≡ b [mod n]` : `a` et `b` ont le même reste dans la division par `n`.
L'arithmétique « de l'horloge » : on peut additionner, multiplier, élever à une puissance
des congruences comme des égalités.

## À prouver
1. `congru_refl`, `congru_symm`, `congru_trans`
2. `congru_add : a ≡ b [mod n] → c ≡ d [mod n] → a + c ≡ b + d [mod n]`
3. `congru_mul : a ≡ b [mod n] → c ≡ d [mod n] → a * c ≡ b * d [mod n]`
4. `congru_pow : a ≡ b [mod n] → a ^ k ≡ b ^ k [mod n]`

## Ressources
- [Congruence sur les entiers (Wikipédia)](https://fr.wikipedia.org/wiki/Congruence_sur_les_entiers)

---
*Exercice* `Arithmetique.Congruences` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Arithmetique.Congruences` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem congru_refl (n a : Nat) : a ≡ a [mod n] := by
  sorry

theorem congru_symm {n a b : Nat} (h : a ≡ b [mod n]) : b ≡ a [mod n] := by
  sorry

theorem congru_trans {n a b c : Nat} (h1 : a ≡ b [mod n]) (h2 : b ≡ c [mod n]) : a ≡ c [mod n] := by
  sorry

theorem congru_add {n a b c d : Nat} (h1 : a ≡ b [mod n]) (h2 : c ≡ d [mod n]) :
    a + c ≡ b + d [mod n] := by
  sorry

theorem congru_mul {n a b c d : Nat} (h1 : a ≡ b [mod n]) (h2 : c ≡ d [mod n]) :
    a * c ≡ b * d [mod n] := by
  sorry

theorem congru_pow {n a b : Nat} (h : a ≡ b [mod n]) (k : Nat) : a ^ k ≡ b ^ k [mod n] := by
  sorry

end Parcours.Arith

#verifier
