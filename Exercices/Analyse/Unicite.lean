import Exercices.Analyse.ValeurAbsolue

/-!
# Unicité de la limite

Une suite ne peut pas tendre vers deux limites différentes. Ce qui justifie de parler de « **la** limite ».

## À prouver
`limite_unique : Tend u l → Tend u l' → l = l'`

---
*Exercice* `Analyse.Unicite` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Analyse.Unicite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Analyse

theorem limite_unique {u : Suite} {l l' : Rat} (h : Tend u l) (h' : Tend u l') : l = l' := by
  sorry

end Parcours.Analyse

#verifier
