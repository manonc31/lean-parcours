/- @parcours
titre: Nim à plusieurs tas et le XOR
difficulte: 3
requiert: Jeux.Nim
indice: Suppose par l'absurde que `a' ^^^ b ^^^ c = 0`. Comme `a ^^^ b ^^^ c = 0` aussi, les deux sont égaux.
indice: « Simplifie » par `b ^^^ c` : `x = x ^^^ y ^^^ y` (`Nat.xor_assoc`, `Nat.xor_self`, `Nat.xor_zero`). On obtient `a' = a`, ce qui contredit `a' < a`.
-/
import Solutions.Recurrence.Definitions

/-!
# Nim à plusieurs tas et le XOR

Le vrai jeu de Nim : plusieurs tas, on retire autant qu'on veut d'**un seul** tas, celui qui prend
la dernière allumette gagne. Charles Bouton (1901) a trouvé la clé : écrire les tailles en binaire
et faire le **ou exclusif** (XOR, noté `^^^`) bit à bit. La position est perdante pour le joueur
au trait si et seulement si le XOR vaut 0.

Ici, la moitié facile du théorème de Bouton, avec trois tas `a, b, c` : depuis une position
de XOR nul, **tout** coup mène à une position de XOR non nul. (L'autre moitié est le boss suivant.)

## À prouver
`depuis_zero : a ^^^ b ^^^ c = 0 → a' < a → a' ^^^ b ^^^ c ≠ 0`

## Ressources
- [Jeu de Nim, stratégie gagnante (Wikipédia)](https://fr.wikipedia.org/wiki/Jeux_de_Nim)
- [Fonction OU exclusif (Wikipédia)](https://fr.wikipedia.org/wiki/Fonction_OU_exclusif)
-/

namespace Parcours.Jeux

theorem depuis_zero (a b c a' : Nat) (h : a ^^^ b ^^^ c = 0) (ha : a' < a) : a' ^^^ b ^^^ c ≠ 0 := by -- @exo
  intro h'
  have e : a' ^^^ (b ^^^ c) = a ^^^ (b ^^^ c) := by
    rw [← Nat.xor_assoc, ← Nat.xor_assoc, h, h']
  have : a' = a := by
    calc a' = a' ^^^ (b ^^^ c) ^^^ (b ^^^ c) := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      _ = a ^^^ (b ^^^ c) ^^^ (b ^^^ c) := by rw [e]
      _ = a := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  omega

end Parcours.Jeux

#verifier
