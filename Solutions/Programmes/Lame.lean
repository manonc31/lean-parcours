/- @parcours
titre: Le pire cas de l'algorithme d'Euclide
difficulte: 3
requiert: Programmes.DivisionSoustraction
indice: `fib_pos` : prouve en même temps `0 < fib (n + 1)` et `0 < fib (n + 2)` par récurrence.
indice: `fib_mod` : `fib (n + 4) = fib (n + 2) + fib (n + 3)`, et `Nat.add_mod_right`, `Nat.mod_eq_of_lt`.
indice: `lame` : déplie `etapes` avec `rw [etapes]`, puis l'hypothèse de récurrence.
-/
import Solutions.Programmes.Definitions

/-!
# Le pire cas de l'algorithme d'Euclide

Combien d'étapes (divisions) l'algorithme d'Euclide fait-il pour calculer un PGCD ? Gabriel Lamé
(1844) a montré que le pire cas est celui de deux nombres de Fibonacci consécutifs : chaque division
ne fait « reculer » que d'un cran dans la suite. C'est le premier résultat de **complexité
algorithmique** de l'histoire.

## À prouver
1. `fib_pos : 0 < fib (n + 1)` et `fib_lt : fib (n + 2) < fib (n + 3)`
2. `fib_mod : fib (n + 4) % fib (n + 3) = fib (n + 2)`
3. `lame : etapes (fib (n + 3)) (fib (n + 2)) = n + 1`

## Ressources
- [Théorème de Lamé (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Lam%C3%A9)
-/

namespace Parcours.Prog

open Parcours.Recurrence

def etapes (a b : Nat) : Nat := if h : b = 0 then 0 else 1 + etapes b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

theorem fib_pos (n : Nat) : 0 < fib (n + 1) := by -- @exo
  have : ∀ n, 0 < fib (n + 1) ∧ 0 < fib (n + 2) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 2 = n + 3 from rfl, show n + 3 = (n + 1) + 2 from rfl, fib_add_two]
      omega
  exact (this n).1

theorem fib_lt (n : Nat) : fib (n + 2) < fib (n + 3) := by -- @exo
  rw [show n + 3 = (n + 1) + 2 from rfl, fib_add_two]
  show fib (n + 2) < fib (n + 1) + fib (n + 2)
  have := fib_pos n
  omega

theorem fib_mod (n : Nat) : fib (n + 4) % fib (n + 3) = fib (n + 2) := by -- @exo
  rw [show n + 4 = (n + 2) + 2 from rfl, fib_add_two, show n + 2 + 1 = n + 3 from rfl,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (fib_lt n)

theorem lame (n : Nat) : etapes (fib (n + 3)) (fib (n + 2)) = n + 1 := by -- @exo
  induction n with
  | zero =>
    show etapes 2 1 = 1
    rw [etapes]
    simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceDIte]
    rw [show 2 % 1 = 0 from rfl, etapes]
    simp
  | succ n ih =>
    rw [show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl, etapes]
    have h : fib (n + 3) ≠ 0 := Nat.ne_of_gt (fib_pos (n + 2))
    simp only [h, ↓reduceDIte]
    rw [fib_mod, ih]
    omega

end Parcours.Prog

#verifier
