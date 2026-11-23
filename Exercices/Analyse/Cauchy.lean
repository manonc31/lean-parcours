import Exercices.Analyse.ValeurAbsolue

/-!
# Toute suite convergente est de Cauchy

Une suite de **Cauchy** : ses termes finissent par être tous proches **les uns des autres**
(sans parler de limite). Toute suite convergente est de Cauchy. La réciproque est vraie dans
les réels… mais **fausse** dans les rationnels (boss suivant) : c'est exactement ce qui manque à ℚ.

## À prouver
`convergente_cauchy : Tend u l → Cauchy u`

---
*Exercice* `Analyse.Cauchy` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Analyse.Cauchy` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Analyse

theorem convergente_cauchy {u : Suite} {l : Rat} (h : Tend u l) : Cauchy u := by
  sorry

end Parcours.Analyse

#verifier
