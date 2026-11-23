/- @parcours
titre: Le tri par insertion
difficulte: 2
indice: `triInsertion [] = []` et `triInsertion (x :: l) = inserer x (triInsertion l)`.
indice: Les deux preuves : récurrence sur `l`, avec `inserer_perm` et `inserer_trie`.
indice: Pour la permutation : `(inserer_perm x _).trans (ih.cons x)`.
-/
import Solutions.Tris.Insertion

/-!
# Le tri par insertion

Le tri du joueur de cartes : on prend les cartes une par une et on insère chacune à sa place.

## À faire
1. `triInsertion : List Nat → List Nat` (à programmer avec `inserer`)
2. `triInsertion_perm : (triInsertion l).Perm l`
3. `triInsertion_trie : Trie (triInsertion l)`

## Ressources
- [Tri par insertion (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_par_insertion)
-/

namespace Parcours.Tris

def triInsertion : List Nat → List Nat -- @exo
  | [] => []
  | x :: l => inserer x (triInsertion l)

theorem triInsertion_perm (l : List Nat) : (triInsertion l).Perm l := by -- @exo
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih => exact (inserer_perm x _).trans (ih.cons x)

theorem triInsertion_trie (l : List Nat) : Trie (triInsertion l) := by -- @exo
  induction l with
  | nil => exact trie_nil
  | cons x l ih => exact inserer_trie x ih

end Parcours.Tris

#verifier
