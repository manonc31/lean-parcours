import Exercices.Tris.Definitions

/-!
# Insérer dans une liste triée

Programme `inserer x l` qui insère `x` à sa place dans une liste triée `l`, puis prouve :
- que le résultat est une permutation de `x :: l` ;
- que si `l` est triée, le résultat l'est aussi.

## À faire
1. `inserer : Nat → List Nat → List Nat` (à programmer)
2. `inserer_perm : (inserer x l).Perm (x :: l)`
3. `inserer_trie : Trie l → Trie (inserer x l)`

---
*Exercice* `Tris.Insertion` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Tris.Insertion` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tris

def inserer (x : Nat) : List Nat → List Nat :=
  sorry

theorem inserer_perm (x : Nat) (l : List Nat) : (inserer x l).Perm (x :: l) := by
  sorry

theorem inserer_trie (x : Nat) {l : List Nat} (h : Trie l) : Trie (inserer x l) := by
  sorry

end Parcours.Tris

#verifier
