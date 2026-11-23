import Exercices.Algorithmes.Definitions

/-!
# Fibonacci en temps linéaire

La définition naïve `fib (n+2) = fib n + fib (n+1)` recalcule les mêmes valeurs un nombre
exponentiel de fois (`fib 50` prend des minutes). La version itérative garde les deux derniers
termes : `n` étapes seulement.

## À prouver
1. `fibPaire_eq : fibPaire n = (fib n, fib (n + 1))`
2. `fibRapide_eq : fibRapide n = fib n`

---
*Exercice* `Algorithmes.FibRapide` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algorithmes.FibRapide` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algo

open Parcours.Recurrence

def fibPaire : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => ((fibPaire n).2, (fibPaire n).1 + (fibPaire n).2)

def fibRapide (n : Nat) : Nat := (fibPaire n).1

theorem fibPaire_eq (n : Nat) : fibPaire n = (fib n, fib (n + 1)) := by
  sorry

theorem fibRapide_eq (n : Nat) : fibRapide n = fib n := by
  sorry

end Parcours.Algo

#verifier
