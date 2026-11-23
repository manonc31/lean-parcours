import Exercices.Graphes.Definitions

/-!
# Le graphe complet

Dans un tournoi où chacun affronte chacun, avec `n` joueurs, combien de matchs ? C'est le
nombre d'arêtes du **graphe complet** `Kₙ` : `n(n − 1)/2`. On le construit en ajoutant les
sommets un par un : le sommet `n` se relie aux `n` sommets précédents.

## À prouver
1. `aretes_complet : 2 * (complet n).length = n * (n - 1)`
2. `degres_k5` : dans `K₅`, chaque sommet a 4 voisins.

---
*Exercice* `Graphes.GrapheComplet` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Graphes.GrapheComplet` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Graphes

def complet : Nat → Graphe
  | 0 => []
  | n + 1 => complet n ++ (List.range n).map fun j => (j, n)

theorem aretes_complet (n : Nat) : 2 * (complet n).length = n * (n - 1) := by
  sorry

theorem degres_k5 : (List.range 5).all (fun v => degre (complet 5) v == 4) = true := by
  sorry

end Parcours.Graphes

#verifier
