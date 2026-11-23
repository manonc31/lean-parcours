/- @parcours
titre: Le premier des premiers
difficulte: 2
requiert: Arithmetique.FacteurPremier
indice: `premier_deux` : un diviseur `d` de 2 vérifie `d ≤ 2` (`divise_le`) et `d ≠ 0`. `omega` conclut `d = 1 ∨ d = 2`.
indice: `premier_impair` : si `p` est pair, `2 ∣ p` (témoin `p / 2`), donc `2 = 1` ou `2 = p`.
-/
import Solutions.Arithmetique.DiviseOrdre

/-!
# Le premier des premiers

`2` est premier, et c'est le seul premier pair.

## À prouver
1. `premier_deux : Premier 2`
2. `premier_impair : Premier p → p ≠ 2 → p % 2 = 1`
-/

namespace Parcours.Arith

theorem premier_deux : Premier 2 := by -- @exo
  refine ⟨Nat.le_refl 2, fun d hd => ?_⟩
  have hle := divise_le hd (by decide)
  have hd0 : d ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hd
    omega
  omega

theorem premier_impair {p : Nat} (hp : Premier p) (h2 : p ≠ 2) : p % 2 = 1 := by -- @exo
  apply Classical.byContradiction
  intro h
  rcases hp.2 2 ⟨p / 2, by omega⟩ with h' | h' <;> omega

end Parcours.Arith

#verifier
