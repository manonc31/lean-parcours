/- @parcours
titre: Insérer dans une liste triée
difficulte: 3
indice: `inserer x [] = [x]` ; `inserer x (y :: l) = if x ≤ y then x :: y :: l else y :: inserer x l`.
indice: Pour les preuves : récurrence sur `l`, `simp only [inserer]` pour déplier, puis `split` pour séparer les deux cas du `if`.
indice: `inserer_perm`, cas `else` : `y :: inserer x l ~ y :: x :: l ~ x :: y :: l` (`List.Perm.cons`, `List.Perm.swap`).
indice: `inserer_trie`, cas `else` : il faut `y ≤ z` pour tout `z ∈ inserer x l`. Grâce à `inserer_perm`, `z ∈ x :: l`.
-/
import Solutions.Tris.Definitions

/-!
# Insérer dans une liste triée

Programme `inserer x l` qui insère `x` à sa place dans une liste triée `l`, puis prouve :
- que le résultat est une permutation de `x :: l` ;
- que si `l` est triée, le résultat l'est aussi.

## À faire
1. `inserer : Nat → List Nat → List Nat` (à programmer)
2. `inserer_perm : (inserer x l).Perm (x :: l)`
3. `inserer_trie : Trie l → Trie (inserer x l)`
-/

namespace Parcours.Tris

def inserer (x : Nat) : List Nat → List Nat -- @exo
  | [] => [x]
  | y :: l => if x ≤ y then x :: y :: l else y :: inserer x l

theorem inserer_perm (x : Nat) (l : List Nat) : (inserer x l).Perm (x :: l) := by -- @exo
  induction l with
  | nil => exact List.Perm.refl _
  | cons y l ih =>
    simp only [inserer]
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y l)

theorem inserer_trie (x : Nat) {l : List Nat} (h : Trie l) : Trie (inserer x l) := by -- @exo
  induction l with
  | nil => exact List.pairwise_singleton _ x
  | cons y l ih =>
    rw [trie_cons] at h
    simp only [inserer]
    split
    · rw [trie_cons, trie_cons]
      refine ⟨?_, h⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · assumption
      · exact Nat.le_trans ‹_› (h.1 z hz)
    · rw [trie_cons]
      refine ⟨?_, ih h.2⟩
      intro z hz
      rcases List.mem_cons.mp ((inserer_perm x l).mem_iff.mp hz) with rfl | hz
      · omega
      · exact h.1 z hz

end Parcours.Tris

#verifier
