import Exercices.Tris.TriInsertion
import Exercices.Tris.TriFusion
import Exercices.Tris.TriRapide
import Exercices.Tris.Unicite

/-!
# Tous les tris sont d'accord

Trois algorithmes complètement différents… et pourtant, pour **toute** liste, ils donnent le
même résultat. Tu n'as pas besoin de les tester sur des exemples : tu l'as **prouvé**.

## À prouver
`tous_d_accord (l : List Nat) : triInsertion l = triFusion l ∧ triFusion l = triRapide l`

---
*Exercice* `Tris.Coherence` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Tris.Coherence` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tris

theorem tous_d_accord (l : List Nat) : triInsertion l = triFusion l ∧ triFusion l = triRapide l := by
  sorry

end Parcours.Tris

#verifier
