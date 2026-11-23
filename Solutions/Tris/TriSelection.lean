/- @parcours
titre: Le tri par sélection
difficulte: 3
requiert: Tris.TriInsertion
indice: `minL_le` et `minL_mem` : récurrence sur `l` en généralisant `m`.
indice: `List.perm_cons_erase : a ∈ l → l ~ a :: l.erase a`.
indice: Pour `triSelection_trie` : un élément du reste est dans `l.erase m`, donc dans `l` (`List.mem_of_mem_erase`), donc plus grand que `m`.
-/
import Solutions.Tris.Definitions

/-!
# Le tri par sélection

Le tri par sélection : on cherche le **plus petit** élément, on le met en tête, et on recommence
avec le reste. C'est le tri que l'on fait naturellement avec des cartes à jouer étalées sur une
table.

## À prouver
1. `minL_le` : le minimum est plus petit que tout le monde ; `minL_mem` : c'est l'un des éléments.
2. `triSelection_perm : (triSelection l).Perm l`
3. `triSelection_trie : Trie (triSelection l)`

## Ressources
- [Tri par sélection (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_par_s%C3%A9lection)
-/

namespace Parcours.Tris

def minL : Nat → List Nat → Nat
  | m, [] => m
  | m, x :: l => minL (min m x) l

theorem minL_le (m : Nat) (l : List Nat) : minL m l ≤ m ∧ ∀ y ∈ l, minL m l ≤ y := by -- @exo
  induction l generalizing m with
  | nil =>
    refine ⟨Nat.le_refl m, fun y hy => ?_⟩
    simp at hy
  | cons x l ih =>
    simp only [minL, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (min m x)
    refine ⟨by omega, fun y hy => ?_⟩
    rcases hy with rfl | hy
    · omega
    · exact h2 y hy

theorem minL_mem (m : Nat) (l : List Nat) : minL m l ∈ m :: l := by -- @exo
  induction l generalizing m with
  | nil => simp [minL]
  | cons x l ih =>
    simp only [minL]
    have := ih (min m x)
    simp only [List.mem_cons] at this ⊢
    rcases this with h | h
    · rcases Nat.le_total m x with hm | hm
      · left; rw [h, Nat.min_eq_left hm]
      · right; left; rw [h, Nat.min_eq_right hm]
    · right; right; exact h

def triSelection (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: r => minL x r :: triSelection ((x :: r).erase (minL x r))
termination_by l.length
decreasing_by
  rw [List.length_erase_of_mem (minL_mem x r)]
  simp

theorem triSelection_perm (l : List Nat) : (triSelection l).Perm l := by -- @exo
  fun_induction triSelection l with
  | case1 => exact List.Perm.refl _
  | case2 x r ih =>
    exact ((ih.cons _).trans (List.perm_cons_erase (minL_mem x r)).symm)

theorem triSelection_trie (l : List Nat) : Trie (triSelection l) := by -- @exo
  fun_induction triSelection l with
  | case1 => exact trie_nil
  | case2 x r ih =>
    rw [trie_cons]
    refine ⟨fun y hy => ?_, ih⟩
    have hy' := (triSelection_perm _).mem_iff.mp hy
    have hy'' := List.mem_of_mem_erase hy'
    obtain ⟨h1, h2⟩ := minL_le x r
    rcases List.mem_cons.mp hy'' with rfl | h
    · exact h1
    · exact h2 y h

end Parcours.Tris

#verifier
