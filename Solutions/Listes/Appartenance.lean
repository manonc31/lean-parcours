/- @parcours
titre: Appartenance
difficulte: 3
indice: `mem_concat` : récurrence sur `l₁`. Cas `nil` : `x ∈ nil` est faux (`not_mem_nil`). Cas `cons` : `rw [cons_concat, mem_cons, mem_cons, ih]`, puis il reste de la logique (le jeton `logique` est débloqué : `or_assoc` est permis).
indice: `mem_map` : récurrence sur `l`. `rw [map_cons, mem_cons, mem_cons, ih]`, puis de la logique avec des ∃.
-/
import Solutions.Listes.Map

/-!
# Appartenance

`x ∈ l` est défini inductivement : `x` est la tête, ou bien `x` est dans la queue.
Le lemme `mem_cons : x ∈ y ∷ l ↔ x = y ∨ x ∈ l` (dans le cours) est ton meilleur ami.

## À prouver
1. `mem_concat : x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂`
2. `mem_miroir : x ∈ miroir l ↔ x ∈ l`
3. `mem_map : y ∈ map f l ↔ ∃ x, x ∈ l ∧ f x = y`
-/

namespace Parcours.Listes.Liste

variable {α β : Type}

theorem mem_concat (x : α) (l₁ l₂ : Liste α) : x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by -- @exo
  induction l₁ with
  | nil =>
    rw [nil_concat]
    exact ⟨Or.inr, fun h => h.elim (fun h => absurd h (not_mem_nil x)) id⟩
  | cons y l ih =>
    rw [cons_concat, mem_cons, mem_cons, ih, or_assoc]

theorem mem_miroir (x : α) (l : Liste α) : x ∈ miroir l ↔ x ∈ l := by -- @exo
  induction l with
  | nil => exact Iff.rfl
  | cons y l ih =>
    rw [miroir_cons, mem_concat, ih, mem_cons, mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd h (not_mem_nil x)
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h

theorem mem_map (f : α → β) (y : β) (l : Liste α) : y ∈ map f l ↔ ∃ x, x ∈ l ∧ f x = y := by -- @exo
  induction l with
  | nil =>
    exact ⟨fun h => absurd h (not_mem_nil y), fun ⟨x, hx, _⟩ => absurd hx (not_mem_nil x)⟩
  | cons z l ih =>
    rw [map_cons, mem_cons, ih]
    constructor
    · rintro (h | ⟨x, hx, hfx⟩)
      · exact ⟨z, (mem_cons z z l).mpr (Or.inl rfl), h.symm⟩
      · exact ⟨x, (mem_cons x z l).mpr (Or.inr hx), hfx⟩
    · rintro ⟨x, hx, hfx⟩
      rcases (mem_cons x z l).mp hx with rfl | hx
      · exact Or.inl hfx.symm
      · exact Or.inr ⟨x, hx, hfx⟩

end Parcours.Listes.Liste

#verifier
