/- @parcours
titre: Fibonacci par les matrices
difficulte: 3
requiert: Matrices.Associativite, Recurrence.Fibonacci
indice: Récurrence sur `n`. `M2.puiss F (n + 2) = M2.puiss F (n + 1) * F` par définition (`rfl`).
indice: Après `simp only [M2.mul_def, F, M2.mk.injEq]`, utilise `fib_add_two` pour faire apparaître les sommes, et `Int.natCast_add` pour les conversions, puis `grind`.
-/
import Solutions.Matrices.Definitions

/-!
# Fibonacci par les matrices

La matrice `F = ⎛1 1⎞ / ⎝1 0⎠` « fabrique » Fibonacci :
`Fⁿ⁺¹ = ⎛F(n+2)  F(n+1)⎞ / ⎝F(n+1)  F(n)⎠`.
Avec l'exponentiation rapide de matrices, on calcule `F(n)` en `log n` étapes : le millionième
nombre de Fibonacci (208 988 chiffres !) se calcule en une fraction de seconde.

## À prouver
`puissance_fib (n : Nat) : M2.puiss F (n + 1) = ⟨fib (n + 2), fib (n + 1), fib (n + 1), fib n⟩`
(les `fib` sont convertis en `Int`)
-/

namespace Parcours.Matrices

open Parcours.Recurrence

def F : M2 := ⟨1, 1, 1, 0⟩

theorem puissance_fib (n : Nat) :
    M2.puiss F (n + 1) = ⟨(fib (n + 2) : Int), fib (n + 1), fib (n + 1), fib n⟩ := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show M2.puiss F (n + 1 + 1) = M2.puiss F (n + 1) * F from rfl, ih]
    simp only [M2.mul_def, F, M2.mk.injEq]
    rw [show n + 1 + 2 = (n + 1) + 2 from rfl, fib_add_two (n + 1), fib_add_two n]
    simp only [Int.natCast_add]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

end Parcours.Matrices

#verifier
