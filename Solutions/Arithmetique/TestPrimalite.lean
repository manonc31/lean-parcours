/- @parcours
titre: Un test de primalité prouvé
difficulte: 4
requiert: Arithmetique.Deux
indice: Déplie et simplifie : `simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq]`.
indice: Sens `→` : un diviseur `d` de `n` qui n'est ni 1 ni `n` vérifierait `2 ≤ d < n` et `n % d = 0` (`Nat.mul_mod_right`).
indice: Sens `←` : si `n % d = 0` avec `2 ≤ d < n`, alors `d ∣ n` (témoin `n / d`, avec `Nat.div_add_mod`), contradiction.
indice: `premier_97` : `(estPremier_correct 97).mp (by decide)`.
-/
import Solutions.Arithmetique.DiviseOrdre

/-!
# Un test de primalité prouvé

`estPremier n` teste tous les diviseurs possibles (un algorithme lent, mais correct). Prouve qu'il
répond exactement `Premier n`. En récompense : `decide` peut maintenant prouver que 97 est premier !

## À prouver
1. `estPremier_correct : estPremier n = true ↔ Premier n`
2. `premier_97 : Premier 97`
-/

namespace Parcours.Arith

def estPremier (n : Nat) : Bool := 2 ≤ n && (List.range n).all (fun d => d < 2 || n % d != 0)

theorem estPremier_correct (n : Nat) : estPremier n = true ↔ Premier n := by -- @exo
  unfold estPremier
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun d hd => ?_⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hd
      omega
    have hle := divise_le hd (by omega)
    apply Classical.byContradiction
    intro hne
    obtain ⟨k, hk⟩ := hd
    rcases hall d (by omega) with h | h
    · omega
    · apply h
      rw [hk]
      exact Nat.mul_mod_right d k
  · rintro ⟨h2, hp⟩
    refine ⟨h2, fun d _ => ?_⟩
    apply Classical.byContradiction
    intro hne
    have hd2 : 2 ≤ d := by omega
    have hmod : n % d = 0 := by omega
    have hdiv : d ∣ n := ⟨n / d, by have := Nat.div_add_mod n d; omega⟩
    rcases hp d hdiv with h | h <;> omega

theorem premier_97 : Premier 97 := by -- @exo
  exact (estPremier_correct 97).mp (by decide)

end Parcours.Arith

#verifier
