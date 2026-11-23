/- @parcours
titre: Décomposition en facteurs premiers (existence)
difficulte: 3
indice: Récurrence forte sur `n`. Si `n = 1`, la liste vide convient (`[].prod = 1`).
indice: Sinon, `n ≥ 2` a un facteur premier `p`, et `n = p * k` avec `1 ≤ k < n`. Décompose `k`, et ajoute `p` en tête.
indice: `List.prod_cons : (a :: l).prod = a * l.prod` et `List.mem_cons : x ∈ a :: l ↔ x = a ∨ x ∈ l`. (Le jeton `List` est débloqué.)
-/
import Solutions.Arithmetique.FacteurPremier

/-!
# Décomposition en facteurs premiers (existence)

Tout entier `n ≥ 1` est un produit de nombres premiers. On le représente par une liste
`l : List Nat` (les listes de Lean : `[2, 2, 3]` pour 12), avec `l.prod` le produit.

## À prouver
`decomposition (n : Nat) : 1 ≤ n → ∃ l : List Nat, (∀ p ∈ l, Premier p) ∧ l.prod = n`

## Ressources
- [Décomposition en produit de facteurs premiers (Wikipédia)](https://fr.wikipedia.org/wiki/D%C3%A9composition_en_produit_de_facteurs_premiers)
-/

namespace Parcours.Arith

theorem decomposition (n : Nat) (hn : 1 ≤ n) :
    ∃ l : List Nat, (∀ p ∈ l, Premier p) ∧ l.prod = n := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h1 : n = 1
    · exact ⟨[], fun p hp => absurd hp List.not_mem_nil, by rw [h1]; rfl⟩
    · obtain ⟨p, hp, k, hk⟩ := existe_facteur_premier n (by omega)
      have hp2 := hp.1
      have hk0 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, Nat.mul_zero] at hk
          omega
        · exact h0
      have hkn : k < n := by
        have : 2 * k ≤ p * k := Nat.mul_le_mul_right k hp2
        omega
      obtain ⟨l, hl, hprod⟩ := ih k hkn hk0
      refine ⟨p :: l, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact hl q hq
      · rw [List.prod_cons, hprod, hk]

end Parcours.Arith

#verifier
