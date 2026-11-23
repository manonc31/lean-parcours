/- @parcours
titre: Longueur d'une concaténation
difficulte: 2
indice: Récurrence sur `l₁`. Cas `nil` : `0 + n = n` dans `Nat`… `Nat.zero_add` ou `omega` (tu as le droit, le Pont est franchi).
indice: Cas `cons` : `rw [cons_concat, longueur_cons, longueur_cons, ih]` puis `omega`.
-/
import Solutions.Listes.Definitions

/-!
# Longueur d'une concaténation

## À prouver
1. `longueur_concat (l₁ l₂ : Liste α) : longueur (l₁ ++ l₂) = longueur l₁ + longueur l₂`
2. `longueur_eq_zero (l : Liste α) : longueur l = 0 ↔ l = nil`
-/

namespace Parcours.Listes.Liste

variable {α : Type}

theorem longueur_concat (l₁ l₂ : Liste α) : longueur (l₁ ++ l₂) = longueur l₁ + longueur l₂ := by -- @exo
  induction l₁ with
  | nil => exact (Nat.zero_add _).symm
  | cons x l ih =>
    rw [cons_concat, longueur_cons, longueur_cons, ih]
    omega

theorem longueur_eq_zero (l : Liste α) : longueur l = 0 ↔ l = nil := by -- @exo
  cases l with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons x l =>
    constructor
    · intro h
      rw [longueur_cons] at h
      omega
    · intro h
      cases h

end Parcours.Listes.Liste

#verifier
