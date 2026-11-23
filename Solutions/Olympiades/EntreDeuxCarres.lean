/- @parcours
titre: Rien entre deux carrés consécutifs
difficulte: 2
requiert: Olympiades.Parite
indice: Compare `m` et `n` (`Nat.lt_or_ge n m`).
indice: Si `n < m`, alors `n + 1 ≤ m` donc `(n+1)² ≤ m²` (`Nat.mul_le_mul`). Sinon `m² ≤ n²`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Rien entre deux carrés consécutifs

Il n'y a aucun carré parfait strictement entre `n²` et `(n + 1)²`.

## À prouver
`entre_deux_carres : ¬∃ m, n * n < m * m ∧ m * m < (n + 1) * (n + 1)`
-/

namespace Parcours.Olymp

theorem entre_deux_carres (n : Nat) : ¬∃ m, n * n < m * m ∧ m * m < (n + 1) * (n + 1) := by -- @exo
  rintro ⟨m, h1, h2⟩
  rcases Nat.lt_or_ge n m with h | h
  · have : (n + 1) * (n + 1) ≤ m * m := Nat.mul_le_mul h h
    omega
  · have : m * m ≤ n * n := Nat.mul_le_mul h h
    omega

end Parcours.Olymp

#verifier
