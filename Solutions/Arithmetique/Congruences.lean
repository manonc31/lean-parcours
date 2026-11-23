/- @parcours
titre: Les congruences
difficulte: 2
indice: `a ≡ b [mod n]` est par définition `a % n = b % n` : `unfold Congru at *` ou `show _ % n = _ % n`.
indice: `congru_add` : `Nat.add_mod : (a + b) % n = ((a % n) + (b % n)) % n`. Réécris des deux côtés, puis utilise `h1` et `h2`.
indice: `congru_pow` : récurrence sur `k`, `Nat.pow_succ` et `congru_mul`.
-/
import Solutions.Arithmetique.Definitions

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
-/

namespace Parcours.Arith

theorem congru_refl (n a : Nat) : a ≡ a [mod n] := by -- @exo
  rfl

theorem congru_symm {n a b : Nat} (h : a ≡ b [mod n]) : b ≡ a [mod n] := by -- @exo
  exact h.symm

theorem congru_trans {n a b c : Nat} (h1 : a ≡ b [mod n]) (h2 : b ≡ c [mod n]) : a ≡ c [mod n] := by -- @exo
  exact Eq.trans h1 h2

theorem congru_add {n a b c d : Nat} (h1 : a ≡ b [mod n]) (h2 : c ≡ d [mod n]) :
    a + c ≡ b + d [mod n] := by -- @exo
  unfold Congru at *
  rw [Nat.add_mod, h1, h2, ← Nat.add_mod]

theorem congru_mul {n a b c d : Nat} (h1 : a ≡ b [mod n]) (h2 : c ≡ d [mod n]) :
    a * c ≡ b * d [mod n] := by -- @exo
  unfold Congru at *
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

theorem congru_pow {n a b : Nat} (h : a ≡ b [mod n]) (k : Nat) : a ^ k ≡ b ^ k [mod n] := by -- @exo
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    exact congru_mul ih h

end Parcours.Arith

#verifier
