/- @parcours
celebre: 74
titre: La récurrence forte
difficulte: 4
indice: Prouve d'abord un énoncé plus fort par récurrence ordinaire : `have H : ∀ n, ∀ m, m < n → P m`.
indice: Pour `H`, cas `zero` : `m < 0` est impossible (`not_lt_zero`).
indice: Cas `succ n` : si `m < succ n`, alors `m ≤ n` (`le_of_succ_le_succ`). Donc `m < n` ou `m = n` (`lt_iff_le_ne` et un `by_cases`/`Classical.em` sur `m = n`). Si `m = n`, applique `h n ih`.
indice: Conclusion : `exact H (succ n) n (le_refl _)` (car `n < succ n` signifie `succ n ≤ succ n`).
-/
import Solutions.Naturels.Strict

/-!
# La récurrence forte

La récurrence ordinaire : pour prouver `P (n+1)`, on suppose `P n`.
La récurrence **forte** : pour prouver `P n`, on suppose `P m` pour **tous** les `m < n`.

C'est plus puissant en apparence, mais on peut la **déduire** de la récurrence ordinaire !
Elle servira partout : décomposition en facteurs premiers, algorithmes « diviser pour régner »…

## À prouver
`recurrence_forte (P : ℕ → Prop) (h : ∀ n, (∀ m, m < n → P m) → P n) (n : ℕ) : P n`

## Ressources
- [Récurrence forte (Wikipédia)](https://fr.wikipedia.org/wiki/Raisonnement_par_r%C3%A9currence#R%C3%A9currence_forte)
-/

namespace Parcours.ℕ

theorem recurrence_forte (P : ℕ → Prop) (h : ∀ n, (∀ m, m < n → P m) → P n) (n : ℕ) : P n := by -- @exo
  have H : ∀ n, ∀ m, m < n → P m := by
    intro n
    induction n with
    | zero =>
      intro m hm
      exact absurd hm (not_lt_zero m)
    | succ n ih =>
      intro m hm
      have hle : m ≤ n := le_of_succ_le_succ m n hm
      rcases Classical.em (m = n) with he | hne
      · rw [he]
        exact h n ih
      · exact ih m ((lt_iff_le_ne m n).mpr ⟨hle, hne⟩)
  exact H (succ n) n (le_refl _)

end Parcours.ℕ

#verifier
