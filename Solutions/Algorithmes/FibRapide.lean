/- @parcours
titre: Fibonacci en temps linéaire
difficulte: 2
requiert: Recurrence.Fibonacci
indice: Prouve plus fort : `fibPaire n = (fib n, fib (n + 1))`, par récurrence sur `n`.
indice: Cas `n + 1` : `show ((fibPaire n).2, (fibPaire n).1 + (fibPaire n).2) = _`, puis `rw [ih, fib_add_two]`.
-/
import Solutions.Algorithmes.Definitions

/-!
# Fibonacci en temps linéaire

La définition naïve `fib (n+2) = fib n + fib (n+1)` recalcule les mêmes valeurs un nombre
exponentiel de fois (`fib 50` prend des minutes). La version itérative garde les deux derniers
termes : `n` étapes seulement.

## À prouver
1. `fibPaire_eq : fibPaire n = (fib n, fib (n + 1))`
2. `fibRapide_eq : fibRapide n = fib n`
-/

namespace Parcours.Algo

open Parcours.Recurrence

def fibPaire : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => ((fibPaire n).2, (fibPaire n).1 + (fibPaire n).2)

def fibRapide (n : Nat) : Nat := (fibPaire n).1

theorem fibPaire_eq (n : Nat) : fibPaire n = (fib n, fib (n + 1)) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((fibPaire n).2, (fibPaire n).1 + (fibPaire n).2) = _
    rw [ih, fib_add_two]

theorem fibRapide_eq (n : Nat) : fibRapide n = fib n := by -- @exo
  unfold fibRapide
  rw [fibPaire_eq]

end Parcours.Algo

#verifier
