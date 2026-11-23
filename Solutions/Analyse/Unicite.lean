/- @parcours
titre: Unicité de la limite
difficulte: 3
indice: Par l'absurde : si `l ≠ l'`, prends `ε := vabs (l - l') / 2 > 0` (`vabs_pos`).
indice: Au rang `n := max N N'`, `|u n - l| < ε` et `|u n - l'| < ε`. L'inégalité triangulaire appliquée à `(l - u n) + (u n - l')` donne `|l - l'| < 2ε = |l - l'|`. Absurde.
indice: Pour réécrire `l - u n + (u n - l')` en `l - l'` : `have e : … := by grind` puis `rw [e] at t`.
-/
import Solutions.Analyse.ValeurAbsolue

/-!
# Unicité de la limite

Une suite ne peut pas tendre vers deux limites différentes. Ce qui justifie de parler de « **la** limite ».

## À prouver
`limite_unique : Tend u l → Tend u l' → l = l'`
-/

namespace Parcours.Analyse

theorem limite_unique {u : Suite} {l l' : Rat} (h : Tend u l) (h' : Tend u l') : l = l' := by -- @exo
  apply Classical.byContradiction
  intro hne
  have hd : 0 < vabs (l - l') := vabs_pos _ (by grind)
  obtain ⟨N, hN⟩ := h (vabs (l - l') / 2) (by grind)
  obtain ⟨N', hN'⟩ := h' (vabs (l - l') / 2) (by grind)
  have h1 := hN (max N N') (Nat.le_max_left _ _)
  have h2 := hN' (max N N') (Nat.le_max_right _ _)
  rw [vabs_sub_comm] at h1
  have t := inegalite_triangulaire (l - u (max N N')) (u (max N N') - l')
  have e : l - u (max N N') + (u (max N N') - l') = l - l' := by grind
  rw [e] at t
  grind

end Parcours.Analyse

#verifier
