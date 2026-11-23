/- @parcours
titre: Le graphe complet
difficulte: 2
requiert: Graphes.PoigneesDeMains
indice: Récurrence ; `List.length_append`, `List.length_map`, `List.length_range`.
indice: Pour éviter `n − 1`, sépare `n = 0` et `n = k + 1`, puis `grind`.
-/
import Solutions.Graphes.Definitions

/-!
# Le graphe complet

Dans un tournoi où chacun affronte chacun, avec `n` joueurs, combien de matchs ? C'est le
nombre d'arêtes du **graphe complet** `Kₙ` : `n(n − 1)/2`. On le construit en ajoutant les
sommets un par un : le sommet `n` se relie aux `n` sommets précédents.

## À prouver
1. `aretes_complet : 2 * (complet n).length = n * (n - 1)`
2. `degres_k5` : dans `K₅`, chaque sommet a 4 voisins.
-/

namespace Parcours.Graphes

def complet : Nat → Graphe
  | 0 => []
  | n + 1 => complet n ++ (List.range n).map fun j => (j, n)

theorem aretes_complet (n : Nat) : 2 * (complet n).length = n * (n - 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [complet, List.length_append, List.length_map, List.length_range]
    rcases n with _ | k
    · rfl
    · simp only [Nat.add_sub_cancel] at ih ⊢
      grind

theorem degres_k5 : (List.range 5).all (fun v => degre (complet 5) v == 4) = true := by -- @exo
  decide

end Parcours.Graphes

#verifier
