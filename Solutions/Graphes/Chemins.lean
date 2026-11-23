/- @parcours
titre: Être relié
difficulte: 2
indice: `relie_trans` : récurrence sur la première hypothèse (`induction h₁ with`).
indice: `relie_symm` : récurrence sur `h`. Dans le cas `arete`, tu as `Relie g w v'`… utilise `relie_trans` avec le chemin d'une seule arête dans l'autre sens.
-/
import Solutions.Graphes.Definitions

/-!
# Être relié

Deux sommets sont **reliés** s'il existe un chemin (une suite d'arêtes) de l'un à l'autre.
Dans un graphe non orienté, « être relié » est une **relation d'équivalence** : elle découpe
le graphe en **composantes connexes**.

## À prouver
1. `relie_trans : Relie g u v → Relie g v w → Relie g u w`
2. `relie_symm : Relie g u v → Relie g v u`
-/

namespace Parcours.Graphes

/-- `Relie g u w` : il existe un chemin de `u` à `w` dans `g`. -/
inductive Relie (g : Graphe) : Nat → Nat → Prop
  | refl (v : Nat) : Relie g v v
  | arete {u v w : Nat} : ((u, v) ∈ g ∨ (v, u) ∈ g) → Relie g v w → Relie g u w

theorem relie_trans {g : Graphe} {u v w : Nat} (h₁ : Relie g u v) (h₂ : Relie g v w) :
    Relie g u w := by -- @exo
  induction h₁ with
  | refl => exact h₂
  | arete he _ ih => exact Relie.arete he (ih h₂)

theorem relie_symm {g : Graphe} {u v : Nat} (h : Relie g u v) : Relie g v u := by -- @exo
  induction h with
  | refl v => exact Relie.refl v
  | @arete u v w he _ ih =>
    apply relie_trans ih
    exact Relie.arete (he.elim Or.inr Or.inl) (Relie.refl u)

end Parcours.Graphes

#verifier
