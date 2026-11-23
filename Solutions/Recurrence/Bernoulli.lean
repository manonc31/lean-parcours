/- @parcours
titre: L'inégalité de Bernoulli
difficulte: 3
indice: Récurrence sur `n`. Cas `succ` : `(1 + x) ^ (n + 1) = (1 + x) ^ n * (1 + x)` (`Nat.pow_succ`).
indice: Multiplie l'hypothèse de récurrence par `1 + x` : `Nat.mul_le_mul_right (1 + x) ih`.
indice: Il reste `1 + (n + 1) * x ≤ (1 + n * x) * (1 + x)` : développe, la différence est `n * x * x ≥ 0`. `grind` sait le faire.
-/
import Solutions.Recurrence.Definitions

/-!
# L'inégalité de Bernoulli

`(1 + x)ⁿ ≥ 1 + n·x`. Simple, mais elle sert partout (convergence de suites, intérêts composés…).

## À prouver
`bernoulli (n x : Nat) : 1 + n * x ≤ (1 + x) ^ n`

## Ressources
- [Inégalité de Bernoulli (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_de_Bernoulli)
-/

namespace Parcours.Recurrence

theorem bernoulli (n x : Nat) : 1 + n * x ≤ (1 + x) ^ n := by -- @exo
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (1 + n * x) * (1 + x) ≤ (1 + x) ^ n * (1 + x) := Nat.mul_le_mul_right _ ih
    have h3 : 1 + (n + 1) * x ≤ (1 + n * x) * (1 + x) := by grind
    rw [Nat.pow_succ]
    omega

end Parcours.Recurrence

#verifier
