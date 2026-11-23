/- @parcours
titre: Compter les occurrences
difficulte: 2
requiert: Programmes.Accumulateur
indice: Récurrence sur la liste ; `simp only [compter]` déplie la définition.
indice: Pour un `if`, `split` sépare les deux cas, ou `by_cases h : x = a` puis `if_pos h` / `if_neg h`.
-/
import Solutions.Programmes.Definitions

/-!
# Compter les occurrences

`compter a l` compte combien de fois `a` apparaît dans `l`.

## À prouver
1. `compter_append : compter a (l₁ ++ l₂) = compter a l₁ + compter a l₂`
2. `compter_le : compter a l ≤ l.length`
3. `compter_pos : 0 < compter a l ↔ a ∈ l`
-/

namespace Parcours.Prog

def compter (a : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => (if x = a then 1 else 0) + compter a l

theorem compter_append (a : Nat) (l₁ l₂ : List Nat) :
    compter a (l₁ ++ l₂) = compter a l₁ + compter a l₂ := by -- @exo
  induction l₁ with
  | nil => simp [compter]
  | cons x l ih =>
    simp only [List.cons_append, compter, ih]
    omega

theorem compter_le (a : Nat) (l : List Nat) : compter a l ≤ l.length := by -- @exo
  induction l with
  | nil => simp [compter]
  | cons x l ih =>
    simp only [compter, List.length_cons]
    split <;> omega

theorem compter_pos (a : Nat) (l : List Nat) : 0 < compter a l ↔ a ∈ l := by -- @exo
  induction l with
  | nil => simp [compter]
  | cons x l ih =>
    simp only [compter, List.mem_cons]
    by_cases h : x = a
    · subst h
      simp only [↓reduceIte, true_or, iff_true]
      omega
    · simp only [h, ↓reduceIte, Nat.zero_add, ih]
      constructor
      · intro h'
        exact Or.inr h'
      · rintro (h' | h')
        · exact absurd h'.symm h
        · exact h'

end Parcours.Prog

#verifier
