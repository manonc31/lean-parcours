/- @parcours
titre: Déterminant d'une puissance
difficulte: 2
indice: Récurrence sur `n`, avec `det_mul` et `Int.pow_succ`.
-/
import Solutions.Matrices.Determinant

/-!
# Déterminant d'une puissance

`det(Aⁿ) = (det A)ⁿ`. Appliqué à la matrice de Fibonacci (de déterminant −1), on retrouve
l'identité de Cassini !

## À prouver
`det_puiss (A : M2) (n : Nat) : M2.det (M2.puiss A n) = M2.det A ^ n`
-/

namespace Parcours.Matrices

theorem det_puiss (A : M2) (n : Nat) : M2.det (M2.puiss A n) = M2.det A ^ n := by -- @exo
  induction n with
  | zero =>
    rw [Int.pow_zero]
    rfl
  | succ n ih =>
    rw [show M2.puiss A (n + 1) = M2.puiss A n * A from rfl, det_mul, ih, Int.pow_succ]

end Parcours.Matrices

#verifier
