/- @parcours
titre: Fermeture éclair (zip)
difficulte: 3
requiert: Listes.PrendreJeter
indice: Récurrence sur `l₁` en généralisant `l₂`, puis `cases l₂`.
indice: Les cas avec une liste vide : `simp [zip, longueur]`. Le cas récursif : `show`, `ih`, puis `omega` (qui connaît `min`).
-/
import Solutions.Listes.Longueur

/-!
# Fermeture éclair (zip)

`zip [1, 2, 3] [a, b] = [(1, a), (2, b)]` : on assemble deux listes deux à deux, en s'arrêtant à la plus courte.

## À prouver
`longueur_zip : longueur (zip l₁ l₂) = min (longueur l₁) (longueur l₂)`
-/

namespace Parcours.Listes.Liste

def zip {α β : Type} : Liste α → Liste β → Liste (α × β)
  | x ∷ l₁, y ∷ l₂ => (x, y) ∷ zip l₁ l₂
  | _, _ => nil

theorem longueur_zip {α β : Type} (l₁ : Liste α) (l₂ : Liste β) :
    longueur (zip l₁ l₂) = min (longueur l₁) (longueur l₂) := by -- @exo
  induction l₁ generalizing l₂ with
  | nil => simp [zip, longueur]
  | cons x l₁ ih =>
    cases l₂ with
    | nil => simp [zip, longueur]
    | cons y l₂ =>
      show longueur (zip l₁ l₂) + 1 = min (longueur l₁ + 1) (longueur l₂ + 1)
      rw [ih]
      omega

end Parcours.Listes.Liste

#verifier
