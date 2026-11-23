import Exercices.Listes.Longueur

/-!
# Filtrer

`filtre p l` garde les éléments `x` de `l` tels que `p x = true`.

## À prouver
1. `filtre_concat : filtre p (l₁ ++ l₂) = filtre p l₁ ++ filtre p l₂`
2. `longueur_filtre : longueur (filtre p l) ≤ longueur l`

---
*Exercice* `Listes.Filtre` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Listes.Filtre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α : Type}

theorem filtre_concat (p : α → Bool) (l₁ l₂ : Liste α) :
    filtre p (l₁ ++ l₂) = filtre p l₁ ++ filtre p l₂ := by
  sorry

theorem longueur_filtre (p : α → Bool) (l : Liste α) : longueur (filtre p l) ≤ longueur l := by
  sorry

end Parcours.Listes.Liste

#verifier
