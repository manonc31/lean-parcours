import Exercices.Matrices.Definitions

/-!
# Fibonacci par les matrices

La matrice `F = ⎛1 1⎞ / ⎝1 0⎠` « fabrique » Fibonacci :
`Fⁿ⁺¹ = ⎛F(n+2)  F(n+1)⎞ / ⎝F(n+1)  F(n)⎠`.
Avec l'exponentiation rapide de matrices, on calcule `F(n)` en `log n` étapes : le millionième
nombre de Fibonacci (208 988 chiffres !) se calcule en une fraction de seconde.

## À prouver
`puissance_fib (n : Nat) : M2.puiss F (n + 1) = ⟨fib (n + 2), fib (n + 1), fib (n + 1), fib n⟩`
(les `fib` sont convertis en `Int`)

---
*Exercice* `Matrices.Fibonacci` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Matrices.Fibonacci` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Matrices

open Parcours.Recurrence

def F : M2 := ⟨1, 1, 1, 0⟩

theorem puissance_fib (n : Nat) :
    M2.puiss F (n + 1) = ⟨(fib (n + 2) : Int), fib (n + 1), fib (n + 1), fib n⟩ := by
  sorry

end Parcours.Matrices

#verifier
