/- @parcours
titre: Le maximum d'une liste
difficulte: 2
indice: Les deux preuves : récurrence sur `l`. `omega` sait raisonner sur `max`.
indice: `le_maximum` : `List.mem_cons` sépare `y = x` et `y ∈ l`.
indice: `maximum_mem` : dans le cas `x :: l`, si `l = []` c'est `x` ; sinon, le maximum est `x` ou `maximum l` (`Nat.max_def` et `split`, ou `by_cases`).
-/
import Solutions.Algorithmes.Definitions

/-!
# Le maximum d'une liste

Le programme le plus simple qui soit… et sa spécification : le résultat est **plus grand que tous**
les éléments, et c'est **l'un d'eux** (si la liste n'est pas vide).

## À prouver
1. `le_maximum : y ∈ l → y ≤ maximum l`
2. `maximum_mem : l ≠ [] → maximum l ∈ l`
-/

namespace Parcours.Algo

def maximum : List Nat → Nat
  | [] => 0
  | x :: l => max x (maximum l)

theorem le_maximum {y : Nat} {l : List Nat} (h : y ∈ l) : y ≤ maximum l := by -- @exo
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [maximum]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h
      omega

theorem maximum_mem (l : List Nat) (h : l ≠ []) : maximum l ∈ l := by -- @exo
  induction l with
  | nil => exact absurd rfl h
  | cons x l ih =>
    simp only [maximum]
    by_cases hl : l = []
    · subst hl
      simp [maximum]
    · by_cases hx : maximum l ≤ x
      · rw [Nat.max_eq_left hx]
        exact List.mem_cons_self
      · rw [Nat.max_eq_right (by omega)]
        exact List.mem_cons_of_mem x (ih hl)

end Parcours.Algo

#verifier
