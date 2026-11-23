import Exercices.Jeux.NimXor

/-!
# 💀 Le théorème de Bouton

La moitié difficile : depuis une position de XOR **non nul**, il existe toujours un coup qui
ramène le XOR à 0. Avec la moitié facile, cela donne la stratégie gagnante complète de Nim :
« ramène toujours le XOR à 0 ».

Boss sans solution de référence (c'est de la manipulation de bits !).

## À prouver
`bouton : a ^^^ b ^^^ c ≠ 0 → (∃ a' < a, a' ^^^ b ^^^ c = 0) ∨ (∃ b' < b, a ^^^ b' ^^^ c = 0) ∨ (∃ c' < c, a ^^^ b ^^^ c' = 0)`

---
*Exercice* `Jeux.Bouton` · difficulté ★★★★★

💡 Indices : `./parcours indice Jeux.Bouton` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Jeux

theorem bouton (a b c : Nat) (h : a ^^^ b ^^^ c ≠ 0) :
    (∃ a' < a, a' ^^^ b ^^^ c = 0) ∨ (∃ b' < b, a ^^^ b' ^^^ c = 0) ∨
      (∃ c' < c, a ^^^ b ^^^ c' = 0) := by
  sorry

end Parcours.Jeux

#verifier
