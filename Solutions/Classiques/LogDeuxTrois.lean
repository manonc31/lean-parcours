/- @parcours
titre: log₂ 3 est irrationnel
difficulte: 2
requiert: Classiques.CarrePair
indice: `trois_pow_impair` : récurrence, `Nat.pow_succ`, `omega`.
indice: Pour `p ≥ 1`, `2^p = 2^(p-1) × 2` est pair. Pour `p = 0`, `1 = 3^q ≥ 3` : `Nat.pow_le_pow_right`.
-/
import Solutions.Recurrence.Definitions
import Solutions.Listes.Pont

/-!
# log₂ 3 est irrationnel

## Se le représenter
Si `log₂ 3 = p/q`, alors `2^p = 3^q`. Impossible : à gauche un nombre pair (si `p ≥ 1`), à droite
un nombre impair. (C'est aussi pourquoi aucune gamme musicale ne tombe juste : 12 quintes
`(3/2)¹²` ne font jamais exactement 7 octaves `2⁷`.)

## À prouver
1. `trois_pow_impair : 3 ^ b % 2 = 1`
2. `log_deux_trois : 0 < q → 2 ^ p ≠ 3 ^ q`

## Ressources
- [Comma pythagoricien (Wikipédia)](https://fr.wikipedia.org/wiki/Comma_pythagoricien)
-/

namespace Parcours.Classiques

theorem trois_pow_impair (b : Nat) : 3 ^ b % 2 = 1 := by -- @exo
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.pow_succ]
    omega

theorem log_deux_trois (p q : Nat) (hq : 0 < q) : 2 ^ p ≠ 3 ^ q := by -- @exo
  intro h
  have h3 := trois_pow_impair q
  cases p with
  | zero =>
    have : 3 ≤ 3 ^ q := by
      calc 3 = 3 ^ 1 := rfl
        _ ≤ 3 ^ q := Nat.pow_le_pow_right (by omega) hq
    simp at h
    omega
  | succ p =>
    rw [Nat.pow_succ] at h
    omega

end Parcours.Classiques

#verifier
