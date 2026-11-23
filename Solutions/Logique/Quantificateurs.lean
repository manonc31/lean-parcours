/- @parcours
titre: « Tout le monde aime quelqu'un »
difficulte: 2
requiert: Logique.Carroll
indice: `inversion` : `obtain ⟨y, hy⟩ := h`, puis `y` convient pour tout `x`.
indice: `pas_reciproque` : si `y` était égal à tout le monde, il serait égal à `true` et à `false`.
-/
import ParcoursOutils

/-!
# « Tout le monde aime quelqu'un »

« Il existe quelqu'un que tout le monde aime » entraîne « tout le monde aime quelqu'un ». Mais
la réciproque est **fausse** : chacun peut aimer une personne différente ! L'ordre des
quantificateurs `∀` et `∃` compte.

## À prouver
1. `inversion : (∃ y, ∀ x, R x y) → ∀ x, ∃ y, R x y`
2. `pas_reciproque` : avec `R x y := (x = y)` sur `Bool`, chacun « s'aime lui-même » mais personne
   n'est aimé de tous.
-/

namespace Parcours.Logique

theorem inversion {α : Type} (R : α → α → Prop) (h : ∃ y, ∀ x, R x y) : ∀ x, ∃ y, R x y := by -- @exo
  intro x
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy x⟩

theorem pas_reciproque : (∀ x : Bool, ∃ y : Bool, x = y) ∧ ¬ ∃ y : Bool, ∀ x : Bool, x = y := by -- @exo
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  intro ⟨y, hy⟩
  have h1 := hy true
  have h2 := hy false
  rw [← h1] at h2
  exact Bool.noConfusion h2

end Parcours.Logique

#verifier
