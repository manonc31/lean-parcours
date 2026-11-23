import Exercices.Programmes.Definitions

/-!
# Compter les occurrences

`compter a l` compte combien de fois `a` apparaît dans `l`.

## À prouver
1. `compter_append : compter a (l₁ ++ l₂) = compter a l₁ + compter a l₂`
2. `compter_le : compter a l ≤ l.length`
3. `compter_pos : 0 < compter a l ↔ a ∈ l`

---
*Exercice* `Programmes.Compter` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Compter` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def compter (a : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => (if x = a then 1 else 0) + compter a l

theorem compter_append (a : Nat) (l₁ l₂ : List Nat) :
    compter a (l₁ ++ l₂) = compter a l₁ + compter a l₂ := by
  sorry

theorem compter_le (a : Nat) (l : List Nat) : compter a l ≤ l.length := by
  sorry

theorem compter_pos (a : Nat) (l : List Nat) : 0 < compter a l ↔ a ∈ l := by
  sorry

end Parcours.Prog

#verifier
