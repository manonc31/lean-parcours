import Exercices.Tris.Insertion

/-!
# Le tri par insertion

Le tri du joueur de cartes : on prend les cartes une par une et on insère chacune à sa place.

## À faire
1. `triInsertion : List Nat → List Nat` (à programmer avec `inserer`)
2. `triInsertion_perm : (triInsertion l).Perm l`
3. `triInsertion_trie : Trie (triInsertion l)`

## Ressources
- [Tri par insertion (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_par_insertion)

---
*Exercice* `Tris.TriInsertion` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Tris.TriInsertion` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tris

def triInsertion : List Nat → List Nat :=
  sorry

theorem triInsertion_perm (l : List Nat) : (triInsertion l).Perm l := by
  sorry

theorem triInsertion_trie (l : List Nat) : Trie (triInsertion l) := by
  sorry

end Parcours.Tris

#verifier
