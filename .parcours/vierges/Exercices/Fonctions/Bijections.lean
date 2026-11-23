import Exercices.Fonctions.Choix
import Exercices.Fonctions.Inverses

/-!
# Bijections et réciproques

Une fonction est bijective si et seulement si elle a une **réciproque** (un inverse des deux côtés).

## À prouver
`bijective_iff : Bijective f ↔ ∃ g : β → α, (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)`

---
*Exercice* `Fonctions.Bijections` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Fonctions.Bijections` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

variable {α β : Type} {f : α → β}

theorem bijective_iff : Bijective f ↔ ∃ g : β → α, (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) := by
  sorry

end Parcours.Fonctions

#verifier
