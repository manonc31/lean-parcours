/- @parcours
titre: Fusionner deux listes triées
difficulte: 3
indice: `fun_induction fusion l₁ l₂ with` donne 4 cas : `case1 l` (première liste vide), `case2 l hne` (seconde vide), `case3 x l₁ y l₂ hxy ih` (`x ≤ y`), `case4 x l₁ y l₂ hxy ih` (`¬x ≤ y`).
indice: `fusion_perm`, cas 4 : `y :: fusion (x :: l₁) l₂ ~ y :: (x :: l₁ ++ l₂) ~ (x :: l₁) ++ y :: l₂` : `(ih.cons y).trans List.perm_middle.symm`.
indice: `fusion_trie`, cas 3 : la tête `x` est ≤ à tout élément de `fusion l₁ (y :: l₂)`, qui est dans `l₁ ++ y :: l₂` (par `fusion_perm`).
-/
import Solutions.Tris.Definitions

/-!
# Fusionner deux listes triées

`fusion` parcourt deux listes triées en même temps et prend à chaque fois le plus petit des
deux éléments de tête. C'est le cœur du tri fusion.

## À prouver
1. `fusion_perm : (fusion l₁ l₂).Perm (l₁ ++ l₂)`
2. `fusion_trie : Trie l₁ → Trie l₂ → Trie (fusion l₁ l₂)`
-/

namespace Parcours.Tris

def fusion : List Nat → List Nat → List Nat
  | [], l => l
  | l, [] => l
  | x :: l₁, y :: l₂ => if x ≤ y then x :: fusion l₁ (y :: l₂) else y :: fusion (x :: l₁) l₂

theorem fusion_perm (l₁ l₂ : List Nat) : (fusion l₁ l₂).Perm (l₁ ++ l₂) := by -- @exo
  fun_induction fusion l₁ l₂ with
  | case1 l => exact List.Perm.refl _
  | case2 l _ => simp
  | case3 x l₁ y l₂ _ ih => exact ih.cons x
  | case4 x l₁ y l₂ _ ih => exact (ih.cons y).trans List.perm_middle.symm

theorem fusion_trie (l₁ l₂ : List Nat) (h₁ : Trie l₁) (h₂ : Trie l₂) : Trie (fusion l₁ l₂) := by -- @exo
  fun_induction fusion l₁ l₂ with
  | case1 l => exact h₂
  | case2 l _ => exact h₁
  | case3 x l₁ y l₂ hxy ih =>
    rw [trie_cons] at h₁ ⊢
    refine ⟨?_, ih h₁.2 h₂⟩
    intro z hz
    rcases List.mem_append.mp ((fusion_perm _ _).mem_iff.mp hz) with hz | hz
    · exact h₁.1 z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact Nat.le_trans hxy ((trie_cons.mp h₂).1 z hz)
  | case4 x l₁ y l₂ hxy ih =>
    rw [trie_cons] at h₂ ⊢
    refine ⟨?_, ih h₁ h₂.2⟩
    intro z hz
    rcases List.mem_append.mp ((fusion_perm _ _).mem_iff.mp hz) with hz | hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact Nat.le_trans (by omega) ((trie_cons.mp h₁).1 z hz)
    · exact h₂.1 z hz

end Parcours.Tris

#verifier
