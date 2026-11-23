import Exercices.Tris.Definitions

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

---
*Exercice* `Tris.TriRapide` · difficulté ★★★★☆

💡 Indices : `./parcours indice Tris.TriRapide` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

theorem triRapide_perm (l : List Nat) : (triRapide l).Perm l := by
  sorry

theorem triRapide_trie (l : List Nat) : Trie (triRapide l) := by
  sorry

end Parcours.Tris

#verifier
