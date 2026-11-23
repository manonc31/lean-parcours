/- @parcours
titre: Donner un témoin
difficulte: 1
requiert: Logique.Existe
indice: `exact ⟨3, rfl⟩`.
indice: Pour le second, cherche `a` et `b` de tête, puis `exact ⟨a, b, rfl, rfl⟩`.
-/
import ParcoursOutils

/-!
# Donner un témoin

Pour prouver `∃ n, n + 2 = 5`, il suffit de donner `n` : `exact ⟨3, rfl⟩` (le témoin, puis la preuve).

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem temoin : ∃ n : Nat, n + 2 = 5 := by -- @exo
  exact ⟨3, rfl⟩

theorem temoin_double : ∃ a b : Nat, a + b = 10 ∧ a = 2 * b + 1 := by -- @exo
  exact ⟨7, 3, rfl, rfl⟩

end Parcours.Gymnase

#verifier
