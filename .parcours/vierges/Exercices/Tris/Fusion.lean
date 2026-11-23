import Exercices.Tris.Definitions

/-!
# Fusionner deux listes triées

`fusion` parcourt deux listes triées en même temps et prend à chaque fois le plus petit des
deux éléments de tête. C'est le cœur du tri fusion.

## À prouver
1. `fusion_perm : (fusion l₁ l₂).Perm (l₁ ++ l₂)`
2. `fusion_trie : Trie l₁ → Trie l₂ → Trie (fusion l₁ l₂)`

---
*Exercice* `Tris.Fusion` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Tris.Fusion` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tris

def fusion : List Nat → List Nat → List Nat
  | [], l => l
  | l, [] => l
  | x :: l₁, y :: l₂ => if x ≤ y then x :: fusion l₁ (y :: l₂) else y :: fusion (x :: l₁) l₂

theorem fusion_perm (l₁ l₂ : List Nat) : (fusion l₁ l₂).Perm (l₁ ++ l₂) := by
  sorry

theorem fusion_trie (l₁ l₂ : List Nat) (h₁ : Trie l₁) (h₂ : Trie l₂) : Trie (fusion l₁ l₂) := by
  sorry

end Parcours.Tris

#verifier
