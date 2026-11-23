/- @parcours
titre: Concaténer avec la liste vide
difficulte: 1
indice: `nil ++ l = l` est vrai par définition. Mais `l ++ nil = l` demande une récurrence sur `l`.
indice: `induction l with`, cas `cons x l ih` : `rw [cons_concat, ih]`.
-/
import Solutions.Listes.Definitions

/-!
# Concaténer avec la liste vide

Comme `0 + a = a` pour ℕ : un côté est vrai par définition, l'autre demande une récurrence.

## À prouver
`concat_nil (l : Liste α) : l ++ nil = l`
-/

namespace Parcours.Listes.Liste

theorem concat_nil {α : Type} (l : Liste α) : l ++ nil = l := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih => rw [cons_concat, ih]

end Parcours.Listes.Liste

#verifier
