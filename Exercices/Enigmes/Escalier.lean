import Exercices.Recurrence.Definitions
import Exercices.Listes.Pont

/-!
# Monter un escalier

On monte un escalier de `n` marches, une ou deux marches à la fois. De combien de façons ?
`montees n` les énumère toutes : la première enjambée fait 1 ou 2 marches. Réponse : le nombre de
Fibonacci `F(n + 1)` ! (C'est le problème qui a fait découvrir la suite… à des poètes indiens du VIᵉ
siècle, qui comptaient les rythmes de syllabes longues et brèves.)

## À prouver
1. `nombre_montees : (montees n).length = fib (n + 1)`
2. `somme_montees : ∀ l ∈ montees n, l.sum = n` (chaque montée fait bien `n` marches)

---
*Exercice* `Enigmes.Escalier` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Enigmes.Escalier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

open Parcours.Recurrence

def montees : Nat → List (List Nat)
  | 0 => [[]]
  | 1 => [[1]]
  | n + 2 => (montees (n + 1)).map (1 :: ·) ++ (montees n).map (2 :: ·)

theorem nombre_montees (n : Nat) : (montees n).length = fib (n + 1) := by
  sorry

theorem somme_montees (n : Nat) : ∀ l ∈ montees n, l.sum = n := by
  sorry

end Parcours.Enigmes

#verifier
