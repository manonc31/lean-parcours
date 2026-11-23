import Exercices.Recurrence.Definitions

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

---
*Exercice* `Jeux.NimXor` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Jeux.NimXor` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Jeux

theorem depuis_zero (a b c a' : Nat) (h : a ^^^ b ^^^ c = 0) (ha : a' < a) : a' ^^^ b ^^^ c ≠ 0 := by
  sorry

end Parcours.Jeux

#verifier
