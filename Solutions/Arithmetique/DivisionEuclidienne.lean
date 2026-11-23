/- @parcours
titre: La division euclidienne
difficulte: 3
interdit: Nat.div*, Nat.mod*, HDiv*, HMod*, Nat.instDiv*, Nat.instMod*
indice: Existence : récurrence sur `a`. Pour `a + 1`, à partir de `a = b * q + r` : si `r + 1 < b`, garde `q` et prends `r + 1` ; sinon `r + 1 = b` et prends `q + 1` et `0`.
indice: `by_cases hr : r + 1 < b`. Pour le second cas, `rw [Nat.mul_add, Nat.mul_one]` puis `omega`.
indice: Unicité : par l'absurde ou avec `Nat.lt_trichotomy q₁ q₂`. Si `q₁ < q₂`, alors `b * (q₁ + 1) ≤ b * q₂` (`Nat.mul_le_mul_left`), et `omega` trouve la contradiction.
-/
import Solutions.Arithmetique.Definitions

/-!
# La division euclidienne

Pour `b > 0`, tout `a` s'écrit **de façon unique** `a = b·q + r` avec `0 ≤ r < b`.
C'est ce que calculent `a / b` (le quotient) et `a % b` (le reste)… mais ici tu dois le prouver
**sans** utiliser `/` ni `%` (le vérificateur refusera).

## À prouver
1. `division_euclidienne (a b : Nat) (hb : 0 < b) : ∃ q r, a = b * q + r ∧ r < b`
2. `unicite_division : a = b * q₁ + r₁ → a = b * q₂ + r₂ → r₁ < b → r₂ < b → q₁ = q₂ ∧ r₁ = r₂`

## Ressources
- [Division euclidienne (Wikipédia)](https://fr.wikipedia.org/wiki/Division_euclidienne)
-/

namespace Parcours.Arith

theorem division_euclidienne (a b : Nat) (hb : 0 < b) : ∃ q r, a = b * q + r ∧ r < b := by -- @exo
  induction a with
  | zero => exact ⟨0, 0, by rw [Nat.mul_zero], hb⟩
  | succ a ih =>
    obtain ⟨q, r, h, hr⟩ := ih
    by_cases hr' : r + 1 < b
    · exact ⟨q, r + 1, by omega, hr'⟩
    · exact ⟨q + 1, 0, by rw [Nat.mul_add, Nat.mul_one]; omega, hb⟩

theorem unicite_division {a b q₁ r₁ q₂ r₂ : Nat} (h₁ : a = b * q₁ + r₁) (h₂ : a = b * q₂ + r₂)
    (hr₁ : r₁ < b) (hr₂ : r₂ < b) : q₁ = q₂ ∧ r₁ = r₂ := by -- @exo
  have hq : q₁ = q₂ := by
    rcases Nat.lt_trichotomy q₁ q₂ with h | h | h
    · have : b * (q₁ + 1) ≤ b * q₂ := Nat.mul_le_mul_left b h
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · exact h
    · have : b * (q₂ + 1) ≤ b * q₁ := Nat.mul_le_mul_left b h
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
  subst hq
  exact ⟨rfl, by omega⟩

end Parcours.Arith

#verifier
