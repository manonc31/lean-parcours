/- @parcours
titre: Découper une pizza
difficulte: 2
requiert: Classiques.Triangulaires
indice: Récurrence ; `simp only [morceaux]`, puis `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# Découper une pizza

## Se le représenter
Avec `n` coupes droites (sans passer par le même point), combien de morceaux au maximum ? La `n`-ième
coupe croise les `n − 1` précédentes, et traverse donc `n` morceaux, qu'elle coupe chacun en deux :
`n` morceaux de plus. (Le « problème du traiteur paresseux ».) Formule : `(n² + n + 2)/2`.

## À prouver
`pizza (n : Nat) : 2 * morceaux n = n * n + n + 2`

## Ressources
- [Suite du traiteur paresseux (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Lazy_caterer%27s_sequence)
-/

namespace Parcours.Classiques

open Parcours.Recurrence

def morceaux : Nat → Nat
  | 0 => 1
  | n + 1 => morceaux n + (n + 1)

theorem pizza (n : Nat) : 2 * morceaux n = n * n + n + 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [morceaux]
    grind

end Parcours.Classiques

#verifier
