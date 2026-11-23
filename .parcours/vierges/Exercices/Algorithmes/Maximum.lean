import Exercices.Algorithmes.Definitions

/-!
# Le maximum d'une liste

Le programme le plus simple qui soit… et sa spécification : le résultat est **plus grand que tous**
les éléments, et c'est **l'un d'eux** (si la liste n'est pas vide).

## À prouver
1. `le_maximum : y ∈ l → y ≤ maximum l`
2. `maximum_mem : l ≠ [] → maximum l ∈ l`

---
*Exercice* `Algorithmes.Maximum` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algorithmes.Maximum` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algo

def maximum : List Nat → Nat
  | [] => 0
  | x :: l => max x (maximum l)

theorem le_maximum {y : Nat} {l : List Nat} (h : y ∈ l) : y ≤ maximum l := by
  sorry

theorem maximum_mem (l : List Nat) (h : l ≠ []) : maximum l ∈ l := by
  sorry

end Parcours.Algo

#verifier
