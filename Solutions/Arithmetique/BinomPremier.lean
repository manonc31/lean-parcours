/- @parcours
titre: p divise les coefficients C(p, k)
difficulte: 4
indice: Lemme : si `n < p` alors `p` ne divise pas `n!` (récurrence sur `n` + lemme d'Euclide : `p` divisant `(n+1) · n!` diviserait `n + 1 < p` ou `n!`).
indice: D'après `binom_mul_fact`, `C(p,k) · k! · (p-k)! = p!`, et `p ∣ p!`.
indice: Lemme d'Euclide deux fois : `p` divise `C(p,k)`, ou `k!`, ou `(p-k)!`. Les deux derniers sont exclus par le lemme (car `k < p` et `p - k < p`).
-/
import Solutions.Arithmetique.LemmeEuclide
import Solutions.Combinatoire.BinomFact

/-!
# p divise les coefficients C(p, k)

Pour `p` premier et `0 < k < p`, `p` divise `C(p, k)`. Regarde la ligne 7 du triangle :
`1 7 21 35 35 21 7 1` — tous divisibles par 7, sauf les bords !

Cet exercice relie deux branches : l'arithmétique (lemme d'Euclide) et la combinatoire (factorielles).

## À prouver
1. `premier_ne_divise_fact : Premier p → n < p → ¬p ∣ fact n`
2. `premier_divise_binom : Premier p → 0 < k → k < p → p ∣ binom p k`
-/

namespace Parcours.Arith

open Parcours.Combi

theorem premier_ne_divise_fact {p n : Nat} (hp : Premier p) (h : n < p) : ¬p ∣ fact n := by -- @exo
  have hp2 := hp.1
  induction n with
  | zero =>
    intro hd
    have := divise_un hd
    omega
  | succ n ih =>
    intro hd
    rw [fact_succ] at hd
    rcases premier_divise_mul hp hd with h1 | h1
    · have := divise_le h1 (by omega)
      omega
    · exact ih (by omega) h1

theorem premier_divise_binom {p k : Nat} (hp : Premier p) (h0 : 0 < k) (hk : k < p) :
    p ∣ binom p k := by -- @exo
  have hf := binom_mul_fact (n := p) (k := k) (by omega)
  have hpf : p ∣ fact p := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.1; omega⟩
    rw [fact_succ]
    exact divise_mul_droite (divise_refl _) _
  rw [← hf] at hpf
  rcases premier_divise_mul hp hpf with h1 | h1
  · rcases premier_divise_mul hp h1 with h2 | h2
    · exact h2
    · exact absurd h2 (premier_ne_divise_fact hp hk)
  · exact absurd h1 (premier_ne_divise_fact hp (by omega))

end Parcours.Arith

#verifier
