/- @parcours
titre: Bits et nombres binaires
difficulte: 1
genre: cours
requiert: Listes.Pont
-/
import Solutions.Recurrence.Definitions
import Solutions.Listes.Pont

/-!
# Bits et nombres binaires (cours)

Un ordinateur ne connaît que des **bits** : `false` (0) et `true` (1). Un nombre est une liste
de bits, **poids faible en tête** : `[true, false, true]` représente `1 + 0×2 + 1×4 = 5`.

- `b.toNat` : la valeur d'un bit (0 ou 1).
- `valeur l` : la valeur d'une liste de bits.

Les portes logiques : `&&` (ET), `||` (OU), `!` (NON), `xor` (OU exclusif).
Pour vérifier une propriété d'un circuit sur toutes les entrées possibles :
`cases a <;> cases b <;> rfl` (ou `decide`).

## Ressources
- [Système binaire (Wikipédia)](https://fr.wikipedia.org/wiki/Syst%C3%A8me_binaire)
- [Additionneur (Wikipédia)](https://fr.wikipedia.org/wiki/Additionneur)
-/

namespace Parcours.Circuits

/-- La valeur d'une liste de bits (poids faible en tête). -/
def valeur : List Bool → Nat
  | [] => 0
  | b :: l => b.toNat + 2 * valeur l

theorem valeur_nil : valeur [] = 0 := rfl
theorem valeur_cons (b : Bool) (l : List Bool) : valeur (b :: l) = b.toNat + 2 * valeur l := rfl

example : valeur [true, false, true] = 5 := rfl

end Parcours.Circuits
