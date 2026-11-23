/- @parcours
titre: L'algorithme de Brzozowski
difficulte: 5
genre: boss
solution: non
requiert: Informatique.Regex
indice: Lemme clé : `Reconnait (deriv a r) w ↔ Reconnait r (a :: w)`. Par récurrence sur `r`.
indice: Le cas difficile est l'étoile : si `etoile r` reconnaît `a :: w`, le premier « morceau » non vide commence par `a`. Il faut une récurrence sur la dérivation, en ignorant les morceaux vides.
indice: Ensuite, `correspond_correct` se prouve par récurrence sur `w` en généralisant `r`, avec `nullable_correct` pour le cas `[]`.
-/
import Solutions.Informatique.Regex

/-!
# 💀 L'algorithme de Brzozowski

La **dérivée** d'une expression `r` par une lettre `a` est une expression `deriv a r` qui reconnaît
les mots `w` tels que `r` reconnaît `a :: w`. Pour tester si `r` reconnaît un mot, on dérive lettre
par lettre, puis on teste `nullable` : c'est un algorithme élégant (Brzozowski, 1964), sans automate.

Boss sans solution de référence.

## À prouver
`correspond_correct (r : Regex α) (w : List α) : correspond r w = true ↔ Reconnait r w`

## Ressources
- [Dérivée de Brzozowski (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Brzozowski_derivative)
-/

namespace Parcours.Info

open Regex

variable {α : Type} [DecidableEq α]

def deriv (a : α) : Regex α → Regex α
  | vide => vide
  | eps => vide
  | car b => if a = b then eps else vide
  | union r s => union (deriv a r) (deriv a s)
  | concat r s => if nullable r then union (concat (deriv a r) s) (deriv a s) else concat (deriv a r) s
  | etoile r => concat (deriv a r) (etoile r)

def correspond (r : Regex α) : List α → Bool
  | [] => nullable r
  | a :: w => correspond (deriv a r) w

theorem correspond_correct (r : Regex α) (w : List α) : correspond r w = true ↔ Reconnait r w := by -- @exo
  sorry

end Parcours.Info

#verifier
