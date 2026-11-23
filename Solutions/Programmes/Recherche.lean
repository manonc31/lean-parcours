/- @parcours
titre: Chercher dans une liste
difficulte: 1
requiert: Programmes.Accumulateur
indice: Récurrence sur `l`, et `split at h` pour séparer les cas du `if` dans l'hypothèse.
indice: `some y = some x` : `cases h` remplace `x` par `y`.
-/
import Solutions.Programmes.Definitions

/-!
# Chercher dans une liste

`chercher p l` renvoie le premier élément de `l` qui vérifie `p` (ou `none` s'il n'y en a pas).

## À prouver
1. `chercher_some` : si on trouve `x`, alors `x ∈ l` et `p x`.
2. `chercher_none` : si on ne trouve rien, aucun élément ne vérifie `p`.
-/

namespace Parcours.Prog

def chercher (p : Nat → Bool) : List Nat → Option Nat
  | [] => none
  | x :: l => if p x then some x else chercher p l

theorem chercher_some (p : Nat → Bool) (l : List Nat) (x : Nat) (h : chercher p l = some x) :
    x ∈ l ∧ p x = true := by -- @exo
  induction l with
  | nil => simp [chercher] at h
  | cons y l ih =>
    simp only [chercher] at h
    split at h
    · rename_i hy
      cases h
      exact ⟨List.mem_cons_self, hy⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem chercher_none (p : Nat → Bool) (l : List Nat) (h : chercher p l = none) :
    ∀ x ∈ l, p x = false := by -- @exo
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [chercher] at h
    split at h
    · simp at h
    · rename_i hy
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using hy
      · exact ih h x hx

end Parcours.Prog

#verifier
