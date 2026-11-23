/- @parcours
celebre: 52
titre: Le nombre de sous-listes
difficulte: 2
indice: Récurrence sur `l`. Les sous-listes de `x :: l` sont celles de `l` (sans `x`), plus celles de `l` avec `x` devant.
indice: `simp [sousListes, ih, Nat.pow_succ]` puis `omega`.
-/
import Solutions.Combinatoire.Definitions

/-!
# Le nombre de sous-listes

Une liste de longueur `n` a `2ⁿ` sous-listes : pour chaque élément, on choisit de le prendre
ou non. Programme `sousListes` puis prouve-le.

## À faire
1. `sousListes : List α → List (List α)` (déjà programmé, lis-le !)
2. `longueur_sousListes (l : List α) : (sousListes l).length = 2 ^ l.length`
3. `mem_sousListes_nil (l : List α) : [] ∈ sousListes l`
-/

namespace Parcours.Combi

def sousListes {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: l => sousListes l ++ (sousListes l).map (x :: ·)

theorem longueur_sousListes {α : Type} (l : List α) : (sousListes l).length = 2 ^ l.length := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp [sousListes, ih, Nat.pow_succ]
    omega

theorem mem_sousListes_nil {α : Type} (l : List α) : [] ∈ sousListes l := by -- @exo
  induction l with
  | nil => exact List.mem_singleton.mpr rfl
  | cons x l ih => exact List.mem_append_left _ ih

end Parcours.Combi

#verifier
