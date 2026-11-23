/- @parcours
titre: Toute suite convergente est bornée
difficulte: 4
indice: Avec `ε = 1` : à partir d'un rang `N`, `|u n| ≤ |l| + 1` (inégalité triangulaire sur `(u n - l) + l`).
indice: Avant le rang `N`, il n'y a qu'un nombre **fini** de termes : prouve `∀ K, ∃ M, 0 ≤ M ∧ ∀ n, n < K → vabs (u n) ≤ M` par récurrence sur `K` (ajoute `vabs (u K)` à chaque étape).
indice: La borne finale : `M + vabs l + 1`.
-/
import Solutions.Analyse.ValeurAbsolue

/-!
# Toute suite convergente est bornée

Si `u` converge, il existe `M` tel que `|u n| ≤ M` pour tout `n`. L'idée : après un certain rang,
les termes sont proches de la limite ; avant, il n'y en a qu'un nombre fini.

## À prouver
`convergente_bornee : Tend u l → ∃ M, ∀ n, vabs (u n) ≤ M`
-/

namespace Parcours.Analyse

theorem convergente_bornee {u : Suite} {l : Rat} (h : Tend u l) : ∃ M, ∀ n, vabs (u n) ≤ M := by -- @exo
  obtain ⟨N, hN⟩ := h 1 (by grind)
  have hpref : ∀ K, ∃ M, 0 ≤ M ∧ ∀ n, n < K → vabs (u n) ≤ M := by
    intro K
    induction K with
    | zero => exact ⟨0, by grind, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
    | succ K ih =>
      obtain ⟨M, hM0, hM⟩ := ih
      have hK := vabs_nonneg (u K)
      refine ⟨M + vabs (u K), by grind, fun n hn => ?_⟩
      by_cases hnK : n < K
      · have := hM n hnK
        grind
      · have : n = K := by omega
        subst this
        grind
  obtain ⟨M, hM0, hM⟩ := hpref N
  have hl := vabs_nonneg l
  refine ⟨M + vabs l + 1, fun n => ?_⟩
  by_cases hn : n < N
  · have := hM n hn
    grind
  · have h1 := hN n (by omega)
    have t := inegalite_triangulaire (u n - l) l
    have e : u n - l + l = u n := by grind
    rw [e] at t
    grind

end Parcours.Analyse

#verifier
