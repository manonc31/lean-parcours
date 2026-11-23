import Exercices.Recurrence.Definitions

/-!
# Un Fibonacci sur trois est pair

## Se le représenter
`0, 1, 1, 2, 3, 5, 8, 13, 21, 34…` : pair, impair, impair, pair, impair, impair… Le motif se
répète car impair + impair = pair, impair + pair = impair, pair + impair = impair.

## À prouver
1. `motif : fib (3k) % 2 = 0 ∧ fib (3k + 1) % 2 = 1 ∧ fib (3k + 2) % 2 = 1`
2. `fib_pair : fib n % 2 = 0 ↔ n % 3 = 0`

---
*Exercice* `Classiques.FibPair` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.FibPair` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem motif (k : Nat) : fib (3 * k) % 2 = 0 ∧ fib (3 * k + 1) % 2 = 1 ∧ fib (3 * k + 2) % 2 = 1 := by
  sorry

theorem fib_pair (n : Nat) : fib n % 2 = 0 ↔ n % 3 = 0 := by
  sorry

end Parcours.Classiques

#verifier
