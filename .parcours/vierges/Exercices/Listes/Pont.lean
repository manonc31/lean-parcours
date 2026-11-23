import Exercices.Listes.Map

/-!
# 🌉 Le pont vers les listes de Lean

Les listes de Lean (`List α`, écrites `[a, b, c]` avec `::` et `++`) sont exactement tes `Liste α`.
Construis les traductions dans les deux sens et prouve qu'elles respectent tout.

🔑 **Récompense** : débloque le jeton **`List`** : tous les lemmes `List.*` de la bibliothèque
(et `simp` sur les listes) deviennent purs pour la suite.

## À faire
1. `versList : Liste α → List α` et `depuisList : List α → Liste α` (à programmer)
2. `depuis_vers (l : Liste α) : depuisList (versList l) = l`
3. `vers_depuis (l : List α) : versList (depuisList l) = l`
4. `versList_concat : versList (l₁ ++ l₂) = versList l₁ ++ versList l₂`
5. `longueur_eq_length : longueur l = (versList l).length`
6. `versList_map : versList (map f l) = (versList l).map f`

---
*Exercice* `Listes.Pont` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Listes.Pont` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α β : Type}

def versList : Liste α → List α :=
  sorry

def depuisList : List α → Liste α :=
  sorry

theorem depuis_vers (l : Liste α) : depuisList (versList l) = l := by
  sorry

theorem vers_depuis (l : List α) : versList (depuisList l) = l := by
  sorry

theorem versList_concat (l₁ l₂ : Liste α) : versList (l₁ ++ l₂) = versList l₁ ++ versList l₂ := by
  sorry

theorem longueur_eq_length (l : Liste α) : longueur l = (versList l).length := by
  sorry

theorem versList_map (f : α → β) (l : Liste α) : versList (map f l) = (versList l).map f := by
  sorry

end Parcours.Listes.Liste

#verifier
