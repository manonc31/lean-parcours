import Exercices.Tris.Fusion

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

---
*Exercice* `Tris.TriFusion` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Tris.TriFusion` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tris

def triFusion (l : List Nat) : List Nat :=
  if h : l.length < 2 then l
  else fusion (triFusion (l.take (l.length / 2))) (triFusion (l.drop (l.length / 2)))
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

theorem triFusion_perm (l : List Nat) : (triFusion l).Perm l := by
  sorry

theorem triFusion_trie (l : List Nat) : Trie (triFusion l) := by
  sorry

end Parcours.Tris

#verifier
