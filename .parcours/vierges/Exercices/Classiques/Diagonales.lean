import Exercices.Arithmetique.Definitions

/-!
# Les diagonales d'un polygone

## Se le représenter
Un carré a 2 diagonales, un pentagone 5, un hexagone 9. Quand on ajoute un sommet à un polygone à `n`
côtés, le nouveau sommet se relie à `n − 2` sommets non voisins, et l'ancien côté devient une diagonale :
`n − 1` diagonales de plus. Formule : `n(n − 3)/2`.

Ici, `diag k` est le nombre de diagonales d'un polygone à `k + 3` côtés.

## À prouver
`diagonales (k : Nat) : 2 * diag k = (k + 3) * k`

---
*Exercice* `Classiques.Diagonales` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.Diagonales` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

def diag : Nat → Nat
  | 0 => 0
  | k + 1 => diag k + (k + 2)

theorem diagonales (k : Nat) : 2 * diag k = (k + 3) * k := by
  sorry

end Parcours.Classiques

#verifier
