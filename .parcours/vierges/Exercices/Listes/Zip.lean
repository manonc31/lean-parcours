import Exercices.Listes.Longueur

/-!
# Fermeture éclair (zip)

`zip [1, 2, 3] [a, b] = [(1, a), (2, b)]` : on assemble deux listes deux à deux, en s'arrêtant à la plus courte.

## À prouver
`longueur_zip : longueur (zip l₁ l₂) = min (longueur l₁) (longueur l₂)`

---
*Exercice* `Listes.Zip` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Listes.Zip` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

def zip {α β : Type} : Liste α → Liste β → Liste (α × β)
  | x ∷ l₁, y ∷ l₂ => (x, y) ∷ zip l₁ l₂
  | _, _ => nil

theorem longueur_zip {α β : Type} (l₁ : Liste α) (l₂ : Liste β) :
    longueur (zip l₁ l₂) = min (longueur l₁) (longueur l₂) := by
  sorry

end Parcours.Listes.Liste

#verifier
