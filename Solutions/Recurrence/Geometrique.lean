/- @parcours
celebre: 66
titre: Les sommes géométriques
difficulte: 3
indice: `somme_puissances_deux` : récurrence ; `rw [somme_succ, Nat.pow_succ]`, puis `omega` avec `ih`.
indice: Pour la version générale, écris `r = s + 1` : `obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩`. Alors `r - 1 = s` (`Nat.add_sub_cancel`).
indice: Puis récurrence : `rw [somme_succ, Nat.pow_succ]` et `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# Les sommes géométriques

`1 + 2 + 4 + ⋯ + 2ⁿ⁻¹ = 2ⁿ - 1` : c'est pour ça que le plus grand nombre sur `n` bits est `2ⁿ - 1`.
Plus généralement : `(r - 1)(1 + r + ⋯ + rⁿ⁻¹) = rⁿ - 1`.

Attention, dans `Nat`, `a - b = 0` quand `b > a` : on évite les soustractions en écrivant
« `+ 1` » de l'autre côté.

## À prouver
1. `somme_puissances_deux (n : Nat) : somme (fun i => 2 ^ i) n + 1 = 2 ^ n`
2. `somme_geometrique (r n : Nat) (hr : 1 ≤ r) : (r - 1) * somme (fun i => r ^ i) n + 1 = r ^ n`

## Ressources
- [Série géométrique (Wikipédia)](https://fr.wikipedia.org/wiki/S%C3%A9rie_g%C3%A9om%C3%A9trique)
-/

namespace Parcours.Recurrence

theorem somme_puissances_deux (n : Nat) : somme (fun i => 2 ^ i) n + 1 = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.pow_succ]
    omega

theorem somme_geometrique (r n : Nat) (hr : 1 ≤ r) :
    (r - 1) * somme (fun i => r ^ i) n + 1 = r ^ n := by -- @exo
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.pow_succ]
    grind

end Parcours.Recurrence

#verifier
