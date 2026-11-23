import Exercices.Tris.Definitions

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

---
*Exercice* `Tris.TriSelection` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Tris.TriSelection` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tris

def minL : Nat → List Nat → Nat
  | m, [] => m
  | m, x :: l => minL (min m x) l

theorem minL_le (m : Nat) (l : List Nat) : minL m l ≤ m ∧ ∀ y ∈ l, minL m l ≤ y := by
  sorry

theorem minL_mem (m : Nat) (l : List Nat) : minL m l ∈ m :: l := by
  sorry

def triSelection (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: r => minL x r :: triSelection ((x :: r).erase (minL x r))
termination_by l.length
decreasing_by
  rw [List.length_erase_of_mem (minL_mem x r)]
  simp

theorem triSelection_perm (l : List Nat) : (triSelection l).Perm l := by
  sorry

theorem triSelection_trie (l : List Nat) : Trie (triSelection l) := by
  sorry

end Parcours.Tris

#verifier
