/- @parcours
titre: Le quantificateur « il existe »
difficulte: 3
requiert: Logique.PourTout
indice: Pour prouver `∃ x, p x`, donne un témoin : `exact ⟨a, ha⟩` (avec `ha : p a`).
indice: Pour utiliser `h : ∃ x, p x`, `obtain ⟨x, hx⟩ := h`.
indice: `reciproque_fausse` : suppose le contraire (`intro h`), applique-le avec `r := fun x y => x = y` sur `Bool`. Tu obtiens un `x` égal à `true` ET à `false`…
indice: Pour conclure, si `h1 : x = true` et `h2 : x = false`, `rw [h1] at h2` donne `h2 : true = false`, et `cases h2` (ou `contradiction`) termine.
-/
import ParcoursOutils

/-!
# Le quantificateur existentiel (∃)

Une preuve de `∃ x, p x` est un **couple** : un témoin `a` et une preuve de `p a`.

- **Construire** : `exact ⟨a, ha⟩` (ou `refine ⟨a, ?_⟩` pour prouver `p a` ensuite).
- **Utiliser** `h : ∃ x, p x` : `obtain ⟨x, hx⟩ := h` (« soit `x` tel que… »).

## À prouver
1. `existe_ou : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x)`
2. `existe_et : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ (∃ x, q x)`
3. `existe_pourtout : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y`
4. `reciproque_fausse` : la réciproque de 3 est **fausse** en général !
   On le montre avec `α := Bool` et `r x y := (x = y)` : chaque `y` est égal à quelqu'un,
   mais personne n'est égal à tout le monde.

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Quantifiers and Equality*.
-/

namespace Parcours.Logique

variable {α : Type} {p q : α → Prop}

theorem existe_ou : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by -- @exo
  constructor
  · rintro ⟨x, hp | hq⟩
    · exact Or.inl ⟨x, hp⟩
    · exact Or.inr ⟨x, hq⟩
  · rintro (⟨x, hp⟩ | ⟨x, hq⟩)
    · exact ⟨x, Or.inl hp⟩
    · exact ⟨x, Or.inr hq⟩

theorem existe_et (h : ∃ x, p x ∧ q x) : (∃ x, p x) ∧ (∃ x, q x) := by -- @exo
  obtain ⟨x, hp, hq⟩ := h
  exact ⟨⟨x, hp⟩, ⟨x, hq⟩⟩

theorem existe_pourtout {r : α → α → Prop} (h : ∃ x, ∀ y, r x y) : ∀ y, ∃ x, r x y := by -- @exo
  intro y
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx y⟩

theorem reciproque_fausse :
    ¬(∀ r : Bool → Bool → Prop, (∀ y, ∃ x, r x y) → ∃ x, ∀ y, r x y) := by -- @exo
  intro h
  obtain ⟨x, hx⟩ := h (fun x y => x = y) (fun y => ⟨y, rfl⟩)
  have h1 : x = true := hx true
  have h2 : x = false := hx false
  rw [h1] at h2
  cases h2

end Parcours.Logique

#verifier
