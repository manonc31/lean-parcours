import Exercices.Listes.ConcatNil
import Exercices.Listes.ConcatAssoc

/-!
# Le miroir

Renverser deux fois une liste redonne la liste de départ. Pour le prouver, il faut d'abord
comprendre comment le miroir interagit avec la concaténation.

## À prouver
1. `miroir_concat (l₁ l₂ : Liste α) : miroir (l₁ ++ l₂) = miroir l₂ ++ miroir l₁`
2. `miroir_miroir (l : Liste α) : miroir (miroir l) = l`

---
*Exercice* `Listes.Miroir` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Listes.Miroir` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α : Type}

theorem miroir_concat (l₁ l₂ : Liste α) : miroir (l₁ ++ l₂) = miroir l₂ ++ miroir l₁ := by
  sorry

theorem miroir_miroir (l : Liste α) : miroir (miroir l) = l := by
  sorry

end Parcours.Listes.Liste

#verifier
