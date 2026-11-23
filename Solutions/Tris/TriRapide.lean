/- @parcours
titre: Le tri rapide
difficulte: 4
indice: `fun_induction triRapide l with` : `case1` (liste vide) et `case2 p l ih1 ih2`.
indice: Permutation : `(ih1.append (ih2.cons p)).trans List.perm_middle`, puis `List.filter_append_perm` (et `.cons p`).
indice: Trié : `trie_append` découpe le but en trois. Les éléments de gauche sont `< p` et ceux de droite `≥ p` : utilise `triRapide_perm` + `List.mem_filter` + `simp` pour le voir.
-/
import Solutions.Tris.Definitions

/-!
# Le tri rapide (quicksort)

On choisit un **pivot** `p` (la tête), on sépare les autres éléments en « plus petits que `p` »
et « plus grands », on trie les deux paquets, et on recolle. Inventé par Tony Hoare en 1959,
c'est l'un des algorithmes les plus utilisés au monde.

## À prouver
1. `triRapide_perm : (triRapide l).Perm l`
2. `triRapide_trie : Trie (triRapide l)`

## Ressources
- [Tri rapide (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_rapide)
-/

namespace Parcours.Tris

set_option wf.preprocess false in
def triRapide : List Nat → List Nat
  | [] => []
  | p :: l => triRapide (l.filter (fun x => decide (x < p))) ++ p :: triRapide (l.filter (fun x => !decide (x < p)))
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem triRapide_perm (l : List Nat) : (triRapide l).Perm l := by -- @exo
  fun_induction triRapide l with
  | case1 => exact List.Perm.refl _
  | case2 p l ih1 ih2 =>
    exact ((ih1.append (ih2.cons p)).trans List.perm_middle).trans
      ((List.filter_append_perm (fun x => decide (x < p)) l).cons p)

theorem triRapide_trie (l : List Nat) : Trie (triRapide l) := by -- @exo
  fun_induction triRapide l with
  | case1 => exact trie_nil
  | case2 p l ih1 ih2 =>
    rw [trie_append, trie_cons]
    refine ⟨ih1, ⟨?_, ih2⟩, ?_⟩
    · intro z hz
      have h := (triRapide_perm _).mem_iff.mp hz
      rw [List.mem_filter] at h
      simp at h
      omega
    · intro a ha b hb
      have ha' := (triRapide_perm _).mem_iff.mp ha
      rw [List.mem_filter] at ha'
      simp at ha'
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · have hb' := (triRapide_perm _).mem_iff.mp hb
        rw [List.mem_filter] at hb'
        simp at hb'
        omega

end Parcours.Tris

#verifier
