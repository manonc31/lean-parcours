import Exercices.Combinatoire.Definitions

/-!
# Le principe multiplicatif

Au restaurant : 3 entrées, 4 plats, 2 desserts. Combien de menus ? `3 × 4 × 2 = 24`. Pour chaque
entrée, on a 4 plats possibles, et pour chaque couple (entrée, plat), 2 desserts : c'est un
**arbre** dont on compte les feuilles.

## À prouver
1. `longueur_produit` : le nombre de couples `(a, b)` est le produit des nombres de choix.
2. `menus` : 24 menus.

---
*Exercice* `Combinatoire.Menus` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Combinatoire.Menus` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem longueur_produit {α β : Type} (l₁ : List α) (l₂ : List β) :
    (l₁.flatMap fun a => l₂.map fun b => (a, b)).length = l₁.length * l₂.length := by
  sorry

def entrees : List String := ["salade", "soupe", "terrine"]
def plats : List String := ["poisson", "poulet", "lasagnes", "curry"]
def desserts : List String := ["glace", "tarte"]

theorem menus : (entrees.flatMap fun e => (plats.flatMap fun p => desserts.map fun d => (p, d)).map
    fun pd => (e, pd)).length = 24 := by
  sorry

end Parcours.Combi

#verifier
