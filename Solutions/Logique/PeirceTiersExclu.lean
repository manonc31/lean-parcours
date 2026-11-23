/- @parcours
titre: Peirce implique le tiers exclu
difficulte: 4
interdit: Classical*, Decidable.em, Decidable.byContradiction
requiert: Logique.Peirce
indice: Applique l'hypothèse de Peirce avec `P := P ∨ ¬P` et `Q := False` : `apply peirce (P ∨ ¬P) False`.
indice: Il reste à prouver `((P ∨ ¬P) → False) → P ∨ ¬P`. Introduis `h`, puis choisis `right`.
indice: C'est le même argument que `non_non_tiers_exclu` !
-/
import ParcoursOutils

/-!
# Peirce ⇒ tiers exclu (sans logique classique !)

Ici, **interdiction** d'utiliser la logique classique (`Classical.em`, `by_cases`, etc.) :
le vérificateur refusera ta preuve si tu le fais.

On suppose que la loi de Peirce est vraie pour toutes les propositions, et on en déduit le
tiers exclu. Autrement dit : en logique constructive, ajouter Peirce comme axiome revient
exactement à passer en logique classique.

## À prouver
`peirce_donne_tiers_exclu : (∀ P Q : Prop, ((P → Q) → P) → P) → ∀ P : Prop, P ∨ ¬P`
-/

namespace Parcours.Logique

theorem peirce_donne_tiers_exclu (peirce : ∀ P Q : Prop, ((P → Q) → P) → P) (P : Prop) : P ∨ ¬P := by -- @exo
  apply peirce (P ∨ ¬P) False
  intro h
  right
  intro hp
  exact h (Or.inl hp)

end Parcours.Logique

#verifier
