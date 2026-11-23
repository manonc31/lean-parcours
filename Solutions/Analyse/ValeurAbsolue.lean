/- @parcours
titre: La valeur absolue
difficulte: 2
indice: Méthode universelle : `unfold vabs`, puis `split` (pour chaque `if`), puis `grind`. Avec plusieurs `vabs`, enchaîne : `split <;> split <;> grind`.
indice: Pour `vabs_lt`, après `unfold vabs; split`, il reste deux équivalences : `grind` les traite (il sait faire `constructor` tout seul).
-/
import Solutions.Analyse.Definitions

/-!
# La valeur absolue

`|x|` est la distance de `x` à `0`. Ses propriétés sont les briques de toute l'analyse.

## À prouver
1. `vabs_nonneg : 0 ≤ vabs x`
2. `vabs_sub_comm : vabs (a - b) = vabs (b - a)` (la distance est symétrique)
3. `inegalite_triangulaire : vabs (a + b) ≤ vabs a + vabs b`
4. `vabs_lt : vabs x < e ↔ -e < x ∧ x < e`
5. `vabs_pos : x ≠ 0 → 0 < vabs x`

## Ressources
- [Inégalité triangulaire (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_triangulaire)
-/

namespace Parcours.Analyse

theorem vabs_nonneg (x : Rat) : 0 ≤ vabs x := by -- @exo
  unfold vabs
  split <;> grind

theorem vabs_sub_comm (a b : Rat) : vabs (a - b) = vabs (b - a) := by -- @exo
  unfold vabs
  split <;> split <;> grind

theorem inegalite_triangulaire (a b : Rat) : vabs (a + b) ≤ vabs a + vabs b := by -- @exo
  unfold vabs
  split <;> split <;> split <;> grind

theorem vabs_lt (x e : Rat) : vabs x < e ↔ -e < x ∧ x < e := by -- @exo
  unfold vabs
  split <;> grind

theorem vabs_pos (x : Rat) (h : x ≠ 0) : 0 < vabs x := by -- @exo
  unfold vabs
  split <;> grind

end Parcours.Analyse

#verifier
