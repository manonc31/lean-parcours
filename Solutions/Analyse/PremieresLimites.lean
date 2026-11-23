/- @parcours
titre: Premières limites
difficulte: 2
indice: `tend_const` : `intro ε hε`, prends `N := 0`, et `vabs (c - c) = 0 < ε` (`unfold vabs; split <;> grind`).
indice: `un_sur_n` : `archimede ε hε` donne `N`. Pour `n ≥ N`, `1/(n+1) ≤ 1/(N+1) < ε`. Le plus simple : `Rat.div_lt_iff` transforme `1 / (n + 1) < ε` en `1 < ε * (n + 1)`.
indice: Pour comparer `ε * (N + 1)` et `ε * (n + 1)` : `Rat.mul_le_mul_of_nonneg_left` avec `(N : Rat) + 1 ≤ n + 1` (vient de `Rat.natCast_le_natCast.mpr hn`).
-/
import Solutions.Analyse.ValeurAbsolue

/-!
# Premières limites

## À prouver
1. `tend_const : Tend (fun _ => c) c` (une suite constante tend vers sa valeur)
2. `un_sur_n : Tend (fun n => 1 / (n + 1)) 0`
-/

namespace Parcours.Analyse

theorem tend_const (c : Rat) : Tend (fun _ => c) c := by -- @exo
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  unfold vabs
  split <;> grind

theorem un_sur_n : Tend (fun n => 1 / ((n : Rat) + 1)) 0 := by -- @exo
  intro ε hε
  obtain ⟨N, hN⟩ := archimede ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : Rat) ≤ (n : Rat) := Rat.natCast_le_natCast.mpr hn
  have h0 : (0 : Rat) ≤ (N : Rat) := Rat.natCast_le_natCast.mpr (Nat.zero_le N)
  have hpos : (0 : Rat) < (n : Rat) + 1 := by grind
  have hposN : (0 : Rat) < (N : Rat) + 1 := by grind
  rw [Rat.div_lt_iff hposN] at hN
  have hmul : ε * ((N : Rat) + 1) ≤ ε * ((n : Rat) + 1) :=
    Rat.mul_le_mul_of_nonneg_left (by grind) (Rat.le_of_lt hε)
  have hlt : 1 / ((n : Rat) + 1) < ε := by
    rw [Rat.div_lt_iff hpos]
    grind
  have hpos' : 0 < 1 / ((n : Rat) + 1) := (Rat.lt_div_iff hpos).mpr (by grind)
  show vabs (1 / ((n : Rat) + 1) - 0) < ε
  unfold vabs
  split <;> grind

end Parcours.Analyse

#verifier
