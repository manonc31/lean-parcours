import Exercices.Programmes.Definitions

/-!
# Le carrousel

`tourner` fait passer le premier élément à la fin : `[1, 2, 3] → [2, 3, 1] → [3, 1, 2] → [1, 2, 3]`.
Après autant de tours que d'éléments, on revient au départ.

## À prouver
1. `tournerN_append : tournerN l₁.length (l₁ ++ l₂) = l₂ ++ l₁`
2. `tour_complet : tournerN l.length l = l`

---
*Exercice* `Programmes.Carrousel` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.Carrousel` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def tourner {α : Type} : List α → List α
  | [] => []
  | x :: l => l ++ [x]

def tournerN {α : Type} : Nat → List α → List α
  | 0, l => l
  | n + 1, l => tournerN n (tourner l)

theorem tournerN_append {α : Type} (l₁ l₂ : List α) :
    tournerN l₁.length (l₁ ++ l₂) = l₂ ++ l₁ := by
  sorry

theorem tour_complet {α : Type} (l : List α) : tournerN l.length l = l := by
  sorry

end Parcours.Prog

#verifier
