/- @parcours
titre: Le tri fusion
difficulte: 3
indice: `fun_induction triFusion l with` : `case1 l h` (moins de 2 éléments) et `case2 l h ih1 ih2` (coupe en deux).
indice: Permutation, cas 2 : `fusion_perm`, puis `ih1.append ih2`, puis `List.take_append_drop` (`simp` le fait).
indice: Trié, cas 1 : une liste de longueur < 2 est `[]` ou `[a]` : `rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩`.
-/
import Solutions.Tris.Fusion

/-!
# Le tri fusion

« Diviser pour régner » : on coupe la liste en deux moitiés, on trie chaque moitié
(récursivement), puis on fusionne. Complexité `n log n` (contre `n²` pour l'insertion).

La définition utilise une récursion **bien fondée** (sur la longueur) : Lean a vérifié qu'elle
termine. À toi de prouver qu'elle trie !

## À prouver
1. `triFusion_perm : (triFusion l).Perm l`
2. `triFusion_trie : Trie (triFusion l)`

## Ressources
- [Tri fusion (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_fusion)
-/

namespace Parcours.Tris

def triFusion (l : List Nat) : List Nat :=
  if h : l.length < 2 then l
  else fusion (triFusion (l.take (l.length / 2))) (triFusion (l.drop (l.length / 2)))
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

theorem triFusion_perm (l : List Nat) : (triFusion l).Perm l := by -- @exo
  fun_induction triFusion l with
  | case1 l _ => exact List.Perm.refl l
  | case2 l _ ih1 ih2 =>
    have h : (l.take (l.length / 2) ++ l.drop (l.length / 2)).Perm l := by simp
    exact (fusion_perm _ _).trans ((ih1.append ih2).trans h)

theorem triFusion_trie (l : List Nat) : Trie (triFusion l) := by -- @exo
  fun_induction triFusion l with
  | case1 l h =>
    rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exact trie_nil
    · exact List.pairwise_singleton _ a
    · simp only [List.length_cons] at h
      omega
  | case2 l _ ih1 ih2 => exact fusion_trie _ _ ih1 ih2

end Parcours.Tris

#verifier
