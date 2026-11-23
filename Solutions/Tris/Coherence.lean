/- @parcours
titre: Tous les tris sont d'accord
difficulte: 2
indice: Applique `trie_unique` : les deux résultats sont triés, et chacun est une permutation de `l`, donc l'un de l'autre (`List.Perm.trans` et `List.Perm.symm`).
-/
import Solutions.Tris.TriInsertion
import Solutions.Tris.TriFusion
import Solutions.Tris.TriRapide
import Solutions.Tris.Unicite

/-!
# Tous les tris sont d'accord

Trois algorithmes complètement différents… et pourtant, pour **toute** liste, ils donnent le
même résultat. Tu n'as pas besoin de les tester sur des exemples : tu l'as **prouvé**.

## À prouver
`tous_d_accord (l : List Nat) : triInsertion l = triFusion l ∧ triFusion l = triRapide l`
-/

namespace Parcours.Tris

theorem tous_d_accord (l : List Nat) : triInsertion l = triFusion l ∧ triFusion l = triRapide l := by -- @exo
  exact ⟨trie_unique _ _ (triInsertion_trie l) (triFusion_trie l)
      ((triInsertion_perm l).trans (triFusion_perm l).symm),
    trie_unique _ _ (triFusion_trie l) (triRapide_trie l)
      ((triFusion_perm l).trans (triRapide_perm l).symm)⟩

end Parcours.Tris

#verifier
