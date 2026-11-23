/- @parcours
titre: Associativité de la concaténation
difficulte: 2
indice: Récurrence sur `l₁`.
indice: Cas `cons` : `rw [cons_concat, cons_concat, cons_concat, ih]`.
-/
import Solutions.Listes.Definitions

/-!
# Associativité de la concaténation

## À prouver
`concat_assoc (l₁ l₂ l₃ : Liste α) : l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃)`
-/

namespace Parcours.Listes.Liste

theorem concat_assoc {α : Type} (l₁ l₂ l₃ : Liste α) : l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃) := by -- @exo
  induction l₁ with
  | nil => rfl
  | cons x l ih => rw [cons_concat, cons_concat, cons_concat, ih]

end Parcours.Listes.Liste

#verifier
