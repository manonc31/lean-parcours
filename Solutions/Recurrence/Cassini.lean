/- @parcours
titre: L'identité de Cassini
difficulte: 4
indice: Travaille dans `Int` : `(x : Int)` convertit un `Nat` en `Int` (`↑x`). `push_cast` n'existe pas sans Mathlib, mais `Int.natCast_add` (`↑(a + b) = ↑a + ↑b`) fait le travail.
indice: Récurrence sur `n`. Cas `succ` : exprime `fib (n + 3) = fib (n + 1) + fib (n + 2)`, convertis en `Int`, et utilise `Int.pow_succ` pour `(-1) ^ (n + 2) = (-1) ^ (n + 1) * (-1)`.
indice: Avec `ih` dans le contexte, `grind` conclut.
-/
import Solutions.Recurrence.Definitions

/-!
# L'identité de Cassini

`F(n+2)·F(n) − F(n+1)² = (−1)ⁿ⁺¹`. Elle est derrière un célèbre « paradoxe » : un carré 8×8
découpé et réassemblé en rectangle 5×13… qui a une case de plus !

On travaille dans `Int` (les entiers relatifs de Lean) à cause du signe.

## À prouver
`cassini (n : Nat) : (fib (n + 2) : Int) * fib n - (fib (n + 1) : Int) ^ 2 = (-1) ^ (n + 1)`

## Ressources
- [Identité de Cassini (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Cassini_and_Catalan_identities)
-/

namespace Parcours.Recurrence

theorem cassini (n : Nat) :
    (fib (n + 2) : Int) * fib n - (fib (n + 1) : Int) ^ 2 = (-1) ^ (n + 1) := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : (fib (n + 3) : Int) = fib (n + 1) + fib (n + 2) := by
      rw [show n + 3 = (n + 1) + 2 by omega, fib_add_two]
      exact Int.natCast_add _ _
    have h2 : (fib (n + 2) : Int) = fib n + fib (n + 1) := by
      rw [fib_add_two]
      exact Int.natCast_add _ _
    rw [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega, h1, Int.pow_succ]
    rw [h2] at ih ⊢
    grind

end Parcours.Recurrence

#verifier
