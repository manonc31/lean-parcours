import Exercices.Naturels.Carre
import Exercices.Naturels.Transfert
import Exercices.Logique.Bilan

/-!
# Sommes, factorielle, Fibonacci (cours)

À partir d'ici, on travaille avec le `Nat` de Lean (le Pont est franchi : `omega` est permis),
et le jeton `anneau` est débloqué (exercice « identité remarquable ») : la tactique **`grind`**
fait les calculs algébriques à ta place. Le cœur de ces exercices, c'est la **récurrence**.

## Définitions
- `somme f n` = `f 0 + f 1 + … + f (n-1)` (la somme des `n` premiers termes) :
  `somme f 0 = 0` et `somme f (n + 1) = somme f n + f n`.
- `fact n` = `n!` : `fact 0 = 1`, `fact (n + 1) = (n + 1) * fact n`.
- `fib n` : `fib 0 = 0`, `fib 1 = 1`, `fib (n + 2) = fib n + fib (n + 1)`.

## Tactiques utiles
- `induction n with | zero => … | succ n ih => …`
- `rw [somme_succ]` déplie la somme ; `omega` (arithmétique linéaire) ; `grind` (calculs non linéaires).
- `Nat.pow_succ : a ^ (n + 1) = a ^ n * a`.

## Ressources
- [Raisonnement par récurrence (Wikipédia)](https://fr.wikipedia.org/wiki/Raisonnement_par_r%C3%A9currence)

---
*Exercice* `Recurrence.Definitions` · difficulté ★☆☆☆☆
-/

namespace Parcours.Recurrence

/-- `somme f n = f 0 + f 1 + ⋯ + f (n - 1)`. -/
def somme (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => somme f n + f n

theorem somme_zero (f : Nat → Nat) : somme f 0 = 0 := rfl
theorem somme_succ (f : Nat → Nat) (n : Nat) : somme f (n + 1) = somme f n + f n := rfl

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_zero : fact 0 = 1 := rfl
theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n := rfl

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_zero : fib 0 = 0 := rfl
theorem fib_one : fib 1 = 1 := rfl
theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

end Parcours.Recurrence
