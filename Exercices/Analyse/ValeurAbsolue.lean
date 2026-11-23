import Exercices.Analyse.Definitions

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

---
*Exercice* `Analyse.ValeurAbsolue` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Analyse.ValeurAbsolue` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Analyse

theorem vabs_nonneg (x : Rat) : 0 ≤ vabs x := by
  sorry

theorem vabs_sub_comm (a b : Rat) : vabs (a - b) = vabs (b - a) := by
  sorry

theorem inegalite_triangulaire (a b : Rat) : vabs (a + b) ≤ vabs a + vabs b := by
  sorry

theorem vabs_lt (x e : Rat) : vabs x < e ↔ -e < x ∧ x < e := by
  sorry

theorem vabs_pos (x : Rat) (h : x ≠ 0) : 0 < vabs x := by
  sorry

end Parcours.Analyse

#verifier
