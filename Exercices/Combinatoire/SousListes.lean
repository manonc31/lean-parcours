import Exercices.Combinatoire.Definitions

/-!
# Le nombre de sous-listes

Une liste de longueur `n` a `2ⁿ` sous-listes : pour chaque élément, on choisit de le prendre
ou non. Programme `sousListes` puis prouve-le.

## À faire
1. `sousListes : List α → List (List α)` (déjà programmé, lis-le !)
2. `longueur_sousListes (l : List α) : (sousListes l).length = 2 ^ l.length`
3. `mem_sousListes_nil (l : List α) : [] ∈ sousListes l`

---
*Exercice* `Combinatoire.SousListes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Combinatoire.SousListes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

def sousListes {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: l => sousListes l ++ (sousListes l).map (x :: ·)

theorem longueur_sousListes {α : Type} (l : List α) : (sousListes l).length = 2 ^ l.length := by
  sorry

theorem mem_sousListes_nil {α : Type} (l : List α) : [] ∈ sousListes l := by
  sorry

end Parcours.Combi

#verifier
