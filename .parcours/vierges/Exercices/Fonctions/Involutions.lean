import Exercices.Fonctions.Inverses

/-!
# Les involutions

Une **involution** est une fonction qui est sa propre réciproque : `f (f x) = x` (comme la négation,
le passage à l'opposé, ou le miroir d'une liste). Une involution est toujours bijective.

## À prouver
`involution_bijective (h : ∀ x, f (f x) = x) : Bijective f`

---
*Exercice* `Fonctions.Involutions` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Fonctions.Involutions` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

theorem involution_bijective {α : Type} {f : α → α} (h : ∀ x, f (f x) = x) : Bijective f := by
  sorry

end Parcours.Fonctions

#verifier
