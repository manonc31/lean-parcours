/- @parcours
celebre: 60
titre: L'identité de Bézout
difficulte: 4
indice: `fun_induction pgcd a b with`. Cas `case1 a` : `pgcd a 0 = a = a * 1 + 0 * 0`.
indice: Cas `case2 a b hb ih` : `ih` donne `x y` avec `pgcd b (a % b) = b * x + (a % b) * y`. Comme `a % b = a - b * (a / b)`, prends `y` et `x - (a / b) * y`.
indice: Dans `Int`, établis d'abord `((a % b : Nat) : Int) + b * ((a / b : Nat) : Int) = a` à partir de `Nat.mod_add_div a b` avec `Int.natCast_add` et `Int.natCast_mul`. Puis `grind`.
-/
import Solutions.Arithmetique.PgcdDivise

/-!
# L'identité de Bézout

Il existe des entiers **relatifs** `x` et `y` tels que `pgcd a b = a·x + b·y`.
On les calcule avec l'algorithme d'Euclide **étendu**.

Ici on travaille dans `Int` (les entiers relatifs de Lean). `(n : Int)` convertit un `Nat`.

## À prouver
`bezout (a b : Nat) : ∃ x y : Int, (pgcd a b : Int) = a * x + b * y`

## Ressources
- [Théorème de Bachet-Bézout (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Bachet-B%C3%A9zout)
-/

namespace Parcours.Arith

theorem bezout (a b : Nat) : ∃ x y : Int, (pgcd a b : Int) = a * x + b * y := by -- @exo
  fun_induction pgcd a b with
  | case1 a => exact ⟨1, 0, by simp⟩
  | case2 a b hb ih =>
    obtain ⟨x, y, h⟩ := ih
    refine ⟨y, x - ((a / b : Nat) : Int) * y, ?_⟩
    have hdiv : ((a % b : Nat) : Int) + (b : Int) * ((a / b : Nat) : Int) = a := by
      rw [← Int.natCast_mul, ← Int.natCast_add, Nat.mod_add_div]
    rw [h]
    grind

end Parcours.Arith

#verifier
