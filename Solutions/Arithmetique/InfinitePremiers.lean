/- @parcours
celebre: 11
titre: Il y a une infinité de nombres premiers
difficulte: 3
indice: Lemme : si `1 ≤ k ≤ n` alors `k ∣ fact n` (récurrence sur `n`, `fact_succ`).
indice: Prends un facteur premier `p` de `fact n + 1`. Si `p ≤ n`, alors `p ∣ fact n`, donc `p ∣ 1` (`divise_sub`), absurde.
-/
import Solutions.Arithmetique.FacteurPremier

/-!
# Il y a une infinité de nombres premiers

La preuve d'Euclide, vieille de 2300 ans : si `p₁, …, pₖ` étaient tous les premiers,
`p₁⋯pₖ + 1` aurait un facteur premier qui n'est aucun d'eux. Ici on utilise `n! + 1`.

## À prouver
1. `divise_fact : 1 ≤ k → k ≤ n → k ∣ fact n`
2. `infinite_premiers (n : Nat) : ∃ p, n < p ∧ Premier p`

## Ressources
- [Théorème d'Euclide sur les nombres premiers (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_d%27Euclide_sur_les_nombres_premiers)
-/

namespace Parcours.Arith

open Parcours.Recurrence

theorem divise_fact {k n : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) : k ∣ fact n := by -- @exo
  induction n with
  | zero => omega
  | succ n ih =>
    rw [fact_succ]
    by_cases h : k = n + 1
    · rw [h]
      exact divise_mul_droite (divise_refl _) _
    · exact divise_trans (ih (by omega)) (divise_mul_gauche _ _)

theorem infinite_premiers (n : Nat) : ∃ p, n < p ∧ Premier p := by -- @exo
  obtain ⟨p, hp, hpd⟩ := existe_facteur_premier (fact n + 1) (by have := fact_pos n; omega)
  refine ⟨p, ?_, hp⟩
  apply Classical.byContradiction
  intro hle
  have h2 := hp.1
  have h1 : p ∣ fact n := divise_fact (by omega) (by omega)
  have := divise_un (divise_sub hpd h1)
  omega

end Parcours.Arith

#verifier
