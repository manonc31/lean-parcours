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

---
*Exercice* `Logique.PeirceTiersExclu` · difficulté ★★★★☆

💡 Indices : `./parcours indice Logique.PeirceTiersExclu` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem peirce_donne_tiers_exclu (peirce : ∀ P Q : Prop, ((P → Q) → P) → P) (P : Prop) : P ∨ ¬P := by
  sorry

end Parcours.Logique

#verifier
