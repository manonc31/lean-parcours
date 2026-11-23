/- @parcours
titre: Premières propriétés de la divisibilité
difficulte: 2
indice: `divise_refl a` : `exact ⟨1, (Nat.mul_one a).symm⟩`.
indice: Pour `divise_trans`, `obtain ⟨k, rfl⟩ := h1` remplace `b` par `a * k` partout ; puis `exact ⟨k * l, Nat.mul_assoc a k l⟩`.
indice: `divise_sub` : de `b + c = a * k` et `b = a * l`, on a `c = a * (k - l)`. `rw [Nat.mul_sub]` puis `omega`.
-/
import Solutions.Arithmetique.Definitions

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
-/

namespace Parcours.Arith

theorem divise_refl (a : Nat) : a ∣ a := by -- @exo
  exact ⟨1, (Nat.mul_one a).symm⟩

theorem divise_zero (a : Nat) : a ∣ 0 := by -- @exo
  exact ⟨0, (Nat.mul_zero a).symm⟩

theorem un_divise (a : Nat) : 1 ∣ a := by -- @exo
  exact ⟨a, (Nat.one_mul a).symm⟩

theorem divise_trans {a b c : Nat} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by -- @exo
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  exact ⟨k * l, Nat.mul_assoc a k l⟩

theorem divise_add {a b c : Nat} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by -- @exo
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  exact ⟨k + l, (Nat.mul_add a k l).symm⟩

theorem divise_mul_droite {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ b * c := by -- @exo
  obtain ⟨k, rfl⟩ := h
  exact ⟨k * c, Nat.mul_assoc a k c⟩

theorem divise_mul_gauche (a b : Nat) : a ∣ b * a := by -- @exo
  exact ⟨b, Nat.mul_comm b a⟩

theorem divise_sub {a b c : Nat} (h1 : a ∣ b + c) (h2 : a ∣ b) : a ∣ c := by -- @exo
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  refine ⟨k - l, ?_⟩
  rw [Nat.mul_sub]
  omega

end Parcours.Arith

#verifier
