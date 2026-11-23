/- @parcours
titre: Le grand examen de logique
difficulte: 3
genre: pont
debloque: logique
requiert: Logique.Distributivite, Logique.Curry, Logique.Egalite, Logique.Equivalence
indice: `bilan_cas` : `rcases Classical.em P with hp | hnp`.
indice: `bilan_absurde` : c'est le barbier en miniature. Montre d'abord `¬P` à partir de `h`.
indice: `bilan_existe`, sens `←` : par cas sur `∀ x, p x`. Si c'est faux, `non_pourtout` donne un `x` tel que `¬p x`.
-/
import Solutions.Logique.NegQuantif

/-!
# 🌉 Le grand examen de logique

Bravo, tu as fait le tour de la logique ! Dernier examen, et en récompense, ce **Pont** débloque
le jeton **`logique`** : pour tous les exercices qui en dépendent, tu pourras utiliser librement
les lemmes de logique de la bibliothèque (`and_comm`, `not_not`, `forall_and`…) et laisser
`simp` manipuler les connecteurs, **sans perdre ton étoile** ⭐. Tu les as tous recodés, tu as gagné le droit de t'en servir.

## À prouver
1. `bilan_cas : (P → Q) → (¬P → Q) → Q`
2. `bilan_absurde : ¬(P ↔ ¬P)`
3. `bilan_existe : (∃ x, p x → q) ↔ ((∀ x, p x) → q)` (avec `α` non vide)
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem bilan_cas (h1 : P → Q) (h2 : ¬P → Q) : Q := by -- @exo
  rcases Classical.em P with hp | hnp
  · exact h1 hp
  · exact h2 hnp

theorem bilan_absurde : ¬(P ↔ ¬P) := by -- @exo
  intro h
  have hnp : ¬P := fun hp => (h.mp hp) hp
  exact hnp (h.mpr hnp)

theorem bilan_existe {α : Type} [Nonempty α] {p : α → Prop} {q : Prop} :
    (∃ x, p x → q) ↔ ((∀ x, p x) → q) := by -- @exo
  constructor
  · rintro ⟨x, hx⟩ hall
    exact hx (hall x)
  · intro h
    rcases Classical.em (∀ x, p x) with hall | hall
    · obtain ⟨a⟩ := ‹Nonempty α›
      exact ⟨a, fun _ => h hall⟩
    · obtain ⟨x, hx⟩ := non_pourtout.mp hall
      exact ⟨x, fun hpx => absurd hpx hx⟩

end Parcours.Logique

#verifier
