import Exercices.Programmes.Definitions

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

---
*Exercice* `Programmes.Lame` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.Lame` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

open Parcours.Recurrence

def etapes (a b : Nat) : Nat := if h : b = 0 then 0 else 1 + etapes b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

theorem fib_pos (n : Nat) : 0 < fib (n + 1) := by
  sorry

theorem fib_lt (n : Nat) : fib (n + 2) < fib (n + 3) := by
  sorry

theorem fib_mod (n : Nat) : fib (n + 4) % fib (n + 3) = fib (n + 2) := by
  sorry

theorem lame (n : Nat) : etapes (fib (n + 3)) (fib (n + 2)) = n + 1 := by
  sorry

end Parcours.Prog

#verifier
