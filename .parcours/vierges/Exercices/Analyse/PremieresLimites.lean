import Exercices.Analyse.ValeurAbsolue

/-!
# Premières limites

## À prouver
1. `tend_const : Tend (fun _ => c) c` (une suite constante tend vers sa valeur)
2. `un_sur_n : Tend (fun n => 1 / (n + 1)) 0`

---
*Exercice* `Analyse.PremieresLimites` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Analyse.PremieresLimites` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Analyse

theorem tend_const (c : Rat) : Tend (fun _ => c) c := by
  sorry

theorem un_sur_n : Tend (fun n => 1 / ((n : Rat) + 1)) 0 := by
  sorry

end Parcours.Analyse

#verifier
