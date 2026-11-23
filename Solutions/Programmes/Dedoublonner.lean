/- @parcours
titre: Supprimer les doublons
difficulte: 2
requiert: Programmes.Compter
indice: Récurrence sur `l`, puis `split` sur le `if x ∈ l`.
indice: `List.nodup_cons : (a :: l).Nodup ↔ a ∉ l ∧ l.Nodup`.
-/
import Solutions.Programmes.Definitions

/-!
# Supprimer les doublons

`dedup` garde un seul exemplaire de chaque élément (le dernier).

## À prouver
1. `mem_dedup : x ∈ dedup l ↔ x ∈ l` (on n'a rien perdu)
2. `nodup_dedup : (dedup l).Nodup` (plus aucun doublon)
-/

namespace Parcours.Prog

def dedup : List Nat → List Nat
  | [] => []
  | x :: l => if x ∈ l then dedup l else x :: dedup l

theorem mem_dedup (x : Nat) (l : List Nat) : x ∈ dedup l ↔ x ∈ l := by -- @exo
  induction l with
  | nil => simp [dedup]
  | cons y l ih =>
    simp only [dedup]
    split
    · rename_i h
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h')
        · exact h
        · exact h'
    · rw [List.mem_cons, ih, List.mem_cons]

theorem nodup_dedup (l : List Nat) : (dedup l).Nodup := by -- @exo
  induction l with
  | nil => simp [dedup]
  | cons y l ih =>
    simp only [dedup]
    split
    · exact ih
    · rename_i h
      rw [List.nodup_cons, mem_dedup]
      exact ⟨h, ih⟩

end Parcours.Prog

#verifier
