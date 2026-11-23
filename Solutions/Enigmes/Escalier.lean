/- @parcours
titre: Monter un escalier
difficulte: 3
requiert: Recurrence.Fibonacci
indice: Récurrence forte (`Nat.strongRecOn`), avec `match n with | 0 | 1 | n + 2`.
indice: Pour le nombre : `List.length_append`, `List.length_map`, puis `fib_add_two`.
indice: Pour la somme : `List.mem_append`, `List.mem_map` décomposent l'appartenance ; `List.sum_cons`.
-/
import Solutions.Recurrence.Definitions
import Solutions.Listes.Pont

/-!
# Monter un escalier

On monte un escalier de `n` marches, une ou deux marches à la fois. De combien de façons ?
`montees n` les énumère toutes : la première enjambée fait 1 ou 2 marches. Réponse : le nombre de
Fibonacci `F(n + 1)` ! (C'est le problème qui a fait découvrir la suite… à des poètes indiens du VIᵉ
siècle, qui comptaient les rythmes de syllabes longues et brèves.)

## À prouver
1. `nombre_montees : (montees n).length = fib (n + 1)`
2. `somme_montees : ∀ l ∈ montees n, l.sum = n` (chaque montée fait bien `n` marches)
-/

namespace Parcours.Enigmes

open Parcours.Recurrence

def montees : Nat → List (List Nat)
  | 0 => [[]]
  | 1 => [[1]]
  | n + 2 => (montees (n + 1)).map (1 :: ·) ++ (montees n).map (2 :: ·)

theorem nombre_montees (n : Nat) : (montees n).length = fib (n + 1) := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      simp only [montees, List.length_append, List.length_map]
      rw [ih (n + 1) (by omega), ih n (by omega), show n + 2 + 1 = (n + 1) + 2 from rfl, fib_add_two (n + 1)]
      omega

theorem somme_montees (n : Nat) : ∀ l ∈ montees n, l.sum = n := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp [montees]
    | 1 => simp [montees]
    | n + 2 =>
      intro l hl
      simp only [montees, List.mem_append, List.mem_map] at hl
      rcases hl with ⟨l', hl', rfl⟩ | ⟨l', hl', rfl⟩
      · simp only [List.sum_cons, ih (n + 1) (by omega) l' hl']
        omega
      · simp only [List.sum_cons, ih n (by omega) l' hl']
        omega

end Parcours.Enigmes

#verifier
