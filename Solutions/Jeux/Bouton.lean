/- @parcours
titre: Le théorème de Bouton
difficulte: 5
genre: boss
solution: non
requiert: Jeux.NimXor
indice: Soit `s = a ^^^ b ^^^ c ≠ 0` et `k` la position de son bit le plus haut (`Nat.log2 s`). Un des trois tas a son bit `k` à 1.
indice: Pour ce tas (disons `a`), `a ^^^ s < a` : les bits au-dessus de `k` ne changent pas, et le bit `k` passe de 1 à 0. Il suffit de jouer `a' := a ^^^ s`.
indice: Lemmes utiles : `Nat.testBit`, `Nat.testBit_xor`, `Nat.lt_of_testBit` (à chercher dans la bibliothèque avec `#check` ou `exact?`).
-/
import Solutions.Jeux.NimXor

/-!
# 💀 Le théorème de Bouton

La moitié difficile : depuis une position de XOR **non nul**, il existe toujours un coup qui
ramène le XOR à 0. Avec la moitié facile, cela donne la stratégie gagnante complète de Nim :
« ramène toujours le XOR à 0 ».

Boss sans solution de référence (c'est de la manipulation de bits !).

## À prouver
`bouton : a ^^^ b ^^^ c ≠ 0 → (∃ a' < a, a' ^^^ b ^^^ c = 0) ∨ (∃ b' < b, a ^^^ b' ^^^ c = 0) ∨ (∃ c' < c, a ^^^ b ^^^ c' = 0)`
-/

namespace Parcours.Jeux

theorem bouton (a b c : Nat) (h : a ^^^ b ^^^ c ≠ 0) :
    (∃ a' < a, a' ^^^ b ^^^ c = 0) ∨ (∃ b' < b, a ^^^ b' ^^^ c = 0) ∨
      (∃ c' < c, a ^^^ b ^^^ c' = 0) := by -- @exo
  sorry

end Parcours.Jeux

#verifier
