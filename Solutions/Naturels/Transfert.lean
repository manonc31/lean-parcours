/- @parcours
titre: Le transfert
difficulte: 2
indice: `apply toNat_injective` : le but devient une égalité dans `Nat`.
indice: `rw [toNat_add, toNat_add]` puis `exact Nat.add_comm _ _` (ou `omega` !).
indice: Pour la multiplication, pareil avec `toNat_mul` et `Nat.mul_comm`.
-/
import Solutions.Naturels.Pont

/-!
# Le transfert

Maintenant que le pont est construit, on peut faire **voyager** les théorèmes de `Nat` vers ton ℕ :
pour prouver une égalité dans ℕ, applique `toNat` des deux côtés (`toNat_injective`), pousse
`toNat` à l'intérieur (`toNat_add`, `toNat_mul`), et utilise la bibliothèque de `Nat`.

Comme cet exercice dépend du Pont, utiliser `Nat.add_comm` ou `omega` ici est **pur** ⭐.

## À prouver (sans récurrence !)
1. `add_comm_bis (a b : ℕ) : a + b = b + a`
2. `mul_comm_bis (a b : ℕ) : a * b = b * a`
3. `exemple_omega (a b : ℕ) : a + (b + a) + b = (a + a) + (b + b)`
-/

namespace Parcours.ℕ

theorem add_comm_bis (a b : ℕ) : a + b = b + a := by -- @exo
  apply toNat_injective
  rw [toNat_add, toNat_add]
  exact Nat.add_comm _ _

theorem mul_comm_bis (a b : ℕ) : a * b = b * a := by -- @exo
  apply toNat_injective
  rw [toNat_mul, toNat_mul]
  exact Nat.mul_comm _ _

theorem exemple_omega (a b : ℕ) : a + (b + a) + b = (a + a) + (b + b) := by -- @exo
  apply toNat_injective
  simp only [toNat_add]
  omega

end Parcours.ℕ

#verifier
