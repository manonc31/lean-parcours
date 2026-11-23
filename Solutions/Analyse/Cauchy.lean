/- @parcours
titre: Toute suite convergente est de Cauchy
difficulte: 3
indice: Applique la convergence avec `ε / 2`. Pour `m, n ≥ N` : `u m - u n = (u m - l) + (l - u n)`.
indice: `vabs_sub_comm` retourne `vabs (u n - l)` en `vabs (l - u n)`. Puis l'inégalité triangulaire et `grind`.
-/
import Solutions.Analyse.ValeurAbsolue

/-!
# Toute suite convergente est de Cauchy

Une suite de **Cauchy** : ses termes finissent par être tous proches **les uns des autres**
(sans parler de limite). Toute suite convergente est de Cauchy. La réciproque est vraie dans
les réels… mais **fausse** dans les rationnels (boss suivant) : c'est exactement ce qui manque à ℚ.

## À prouver
`convergente_cauchy : Tend u l → Cauchy u`
-/

namespace Parcours.Analyse

theorem convergente_cauchy {u : Suite} {l : Rat} (h : Tend u l) : Cauchy u := by -- @exo
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by grind)
  refine ⟨N, fun m n hm hn => ?_⟩
  have h1 := hN m hm
  have h2 := hN n hn
  rw [vabs_sub_comm] at h2
  have t := inegalite_triangulaire (u m - l) (l - u n)
  have e : u m - l + (l - u n) = u m - u n := by grind
  rw [e] at t
  grind

end Parcours.Analyse

#verifier
