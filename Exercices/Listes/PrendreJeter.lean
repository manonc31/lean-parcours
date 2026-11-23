import Exercices.Listes.Longueur

/-!
# Prendre et jeter

`prendre n l` : les `n` premiers éléments. `jeter n l` : tout sauf les `n` premiers.

## À prouver
1. `prendre_jeter : prendre n l ++ jeter n l = l`
2. `longueur_prendre : longueur (prendre n l) = min n (longueur l)`
3. `longueur_jeter : longueur (jeter n l) = longueur l - n`

---
*Exercice* `Listes.PrendreJeter` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Listes.PrendreJeter` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α : Type}

theorem prendre_jeter (n : Nat) (l : Liste α) : prendre n l ++ jeter n l = l := by
  sorry

theorem longueur_prendre (n : Nat) (l : Liste α) : longueur (prendre n l) = min n (longueur l) := by
  sorry

theorem longueur_jeter (n : Nat) (l : Liste α) : longueur (jeter n l) = longueur l - n := by
  sorry

end Parcours.Listes.Liste

#verifier
