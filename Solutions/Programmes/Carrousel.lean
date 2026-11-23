/- @parcours
titre: Le carrousel
difficulte: 3
requiert: Programmes.Accumulateur
indice: Le bon énoncé à prouver par récurrence est le plus général : `tournerN_append`, sur `l₁`, en généralisant `l₂`.
indice: `tourner (x :: (l ++ l₂)) = (l ++ l₂) ++ [x] = l ++ (l₂ ++ [x])` (`List.append_assoc`).
-/
import Solutions.Programmes.Definitions

/-!
# Le carrousel

`tourner` fait passer le premier élément à la fin : `[1, 2, 3] → [2, 3, 1] → [3, 1, 2] → [1, 2, 3]`.
Après autant de tours que d'éléments, on revient au départ.

## À prouver
1. `tournerN_append : tournerN l₁.length (l₁ ++ l₂) = l₂ ++ l₁`
2. `tour_complet : tournerN l.length l = l`
-/

namespace Parcours.Prog

def tourner {α : Type} : List α → List α
  | [] => []
  | x :: l => l ++ [x]

def tournerN {α : Type} : Nat → List α → List α
  | 0, l => l
  | n + 1, l => tournerN n (tourner l)

theorem tournerN_append {α : Type} (l₁ l₂ : List α) :
    tournerN l₁.length (l₁ ++ l₂) = l₂ ++ l₁ := by -- @exo
  induction l₁ generalizing l₂ with
  | nil => simp [tournerN]
  | cons x l ih =>
    simp only [List.length_cons, tournerN, List.cons_append, tourner]
    rw [List.append_assoc, ih]
    simp

theorem tour_complet {α : Type} (l : List α) : tournerN l.length l = l := by -- @exo
  simpa using tournerN_append l []

end Parcours.Prog

#verifier
