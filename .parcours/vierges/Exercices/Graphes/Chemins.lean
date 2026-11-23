import Exercices.Graphes.Definitions

/-!
# Être relié

Deux sommets sont **reliés** s'il existe un chemin (une suite d'arêtes) de l'un à l'autre.
Dans un graphe non orienté, « être relié » est une **relation d'équivalence** : elle découpe
le graphe en **composantes connexes**.

## À prouver
1. `relie_trans : Relie g u v → Relie g v w → Relie g u w`
2. `relie_symm : Relie g u v → Relie g v u`

---
*Exercice* `Graphes.Chemins` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Graphes.Chemins` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Graphes

/-- `Relie g u w` : il existe un chemin de `u` à `w` dans `g`. -/
inductive Relie (g : Graphe) : Nat → Nat → Prop
  | refl (v : Nat) : Relie g v v
  | arete {u v w : Nat} : ((u, v) ∈ g ∨ (v, u) ∈ g) → Relie g v w → Relie g u w

theorem relie_trans {g : Graphe} {u v w : Nat} (h₁ : Relie g u v) (h₂ : Relie g v w) :
    Relie g u w := by
  sorry

theorem relie_symm {g : Graphe} {u v : Nat} (h : Relie g u v) : Relie g v u := by
  sorry

end Parcours.Graphes

#verifier
