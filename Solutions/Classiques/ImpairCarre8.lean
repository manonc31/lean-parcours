/- @parcours
titre: Le carré d'un impair modulo 8
difficulte: 2
requiert: Classiques.Divisible3
indice: Sépare `n` pair (`n = 2k`) et impair (`n = 2k + 1`).
indice: Développe avec `grind` (`(4k+1)² = 16k² + 8k + 1`), puis `omega`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Le carré d'un impair modulo 8

## Se le représenter
`1, 9, 25, 49, 81, …` : tous les carrés impairs valent 1 modulo 8. Car `(2n+1)² = 4n(n+1) + 1`,
et `n(n+1)` est pair.

## À prouver
`impair_carre (n : Nat) : ((2 * n + 1) ^ 2) % 8 = 1`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem impair_carre (n : Nat) : ((2 * n + 1) ^ 2) % 8 = 1 := by -- @exo
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have e : (2 * (2 * k) + 1) ^ 2 = 16 * (k * k) + 8 * k + 1 := by grind
    rw [e]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have e : (2 * (2 * k + 1) + 1) ^ 2 = 16 * (k * k) + 24 * k + 9 := by grind
    rw [e]
    omega

end Parcours.Classiques

#verifier
