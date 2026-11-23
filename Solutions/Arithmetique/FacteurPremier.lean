/- @parcours
titre: Tout nombre a un facteur premier
difficulte: 3
indice: Récurrence forte : `induction n using Nat.strongRecOn with | ind n ih => …` (`ih : ∀ m < n, …`).
indice: Si `n` est premier, c'est fini. Sinon (`by_cases hp : Premier n`), il existe un diviseur `d` de `n` avec `d ≠ 1` et `d ≠ n`. (Pour l'extraire, raisonne par l'absurde.)
indice: Alors `2 ≤ d < n` (`d ≠ 0` car `n ≠ 0`, et `divise_le`), et l'hypothèse de récurrence donne un facteur premier de `d`, qui divise `n` par transitivité.
-/
import Solutions.Arithmetique.DiviseOrdre

/-!
# Tout nombre a un facteur premier

Tout entier `n ≥ 2` est divisible par au moins un nombre premier.

## Récurrence forte sur `Nat`
`induction n using Nat.strongRecOn with | ind n ih => …` : `ih` dit que la propriété
est vraie pour tous les `m < n`.

## À prouver
`existe_facteur_premier (n : Nat) : 2 ≤ n → ∃ p, Premier p ∧ p ∣ n`
-/

namespace Parcours.Arith

theorem existe_facteur_premier (n : Nat) (hn : 2 ≤ n) : ∃ p, Premier p ∧ p ∣ n := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hp : Premier n
    · exact ⟨n, hp, divise_refl n⟩
    · have hd : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
        apply Classical.byContradiction
        intro hne
        apply hp
        refine ⟨hn, fun d hd => ?_⟩
        apply Classical.byContradiction
        intro hd'
        exact hne ⟨d, hd, fun h => hd' (Or.inl h), fun h => hd' (Or.inr h)⟩
      obtain ⟨d, hd, hd1, hdn⟩ := hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        obtain ⟨k, hk⟩ := hd
        omega
      have hdle := divise_le hd (by omega)
      obtain ⟨p, hp, hpd⟩ := ih d (by omega) (by omega)
      exact ⟨p, hp, divise_trans hpd hd⟩

end Parcours.Arith

#verifier
