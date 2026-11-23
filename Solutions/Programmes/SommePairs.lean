/- @parcours
titre: Deux façons de sommer les pairs
difficulte: 1
requiert: Programmes.Accumulateur
indice: Récurrence ; `List.filter_cons` déplie le filtre.
indice: Deux cas selon la parité de `x` : `by_cases h : x % 2 = 0 <;> simp [h]`.
-/
import Solutions.Programmes.Definitions

/-!
# Deux façons de sommer les pairs

Deux programmes pour additionner les nombres pairs d'une liste : avec une boucle et un `if`,
ou en **filtrant** d'abord puis en sommant. Ils calculent la même chose — prouvons-le.

## À prouver
`deux_versions : sommePairsBoucle l = (l.filter (· % 2 == 0)).sum`
-/

namespace Parcours.Prog

def sommePairsBoucle : List Nat → Nat
  | [] => 0
  | x :: l => (if x % 2 = 0 then x else 0) + sommePairsBoucle l

theorem deux_versions (l : List Nat) : sommePairsBoucle l = (l.filter (· % 2 == 0)).sum := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [sommePairsBoucle, List.filter_cons, ih]
    by_cases h : x % 2 = 0 <;> simp [h]

end Parcours.Prog

#verifier
