import Exercices.Listes.Plis
import Exercices.Listes.Longueur

/-!
# Aplatir une liste de listes

`aplatir [[1, 2], [], [3]] = [1, 2, 3]`. Sa longueur est la somme des longueurs.

## À prouver
`longueur_aplatir : longueur (aplatir ll) = somme (map longueur ll)`

---
*Exercice* `Listes.Aplatir` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Listes.Aplatir` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

def aplatir {α : Type} : Liste (Liste α) → Liste α
  | nil => nil
  | l ∷ ll => l ++ aplatir ll

theorem longueur_aplatir {α : Type} (ll : Liste (Liste α)) :
    longueur (aplatir ll) = somme (map longueur ll) := by
  sorry

end Parcours.Listes.Liste

#verifier
