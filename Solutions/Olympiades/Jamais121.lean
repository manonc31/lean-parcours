/- @parcours
titre: n² + 3n + 5 et 121
difficulte: 3
requiert: Olympiades.CinqTrente
indice: Écris `n = 121q + r` avec `r < 121` (`Nat.div_add_mod`).
indice: Développe avec `grind`, puis `Nat.mul_add_mod : (m * x + y) % m = y % m`.
indice: Il reste 121 cas : efface les hypothèses qui parlent de `q` (`clear`), puis `revert r` et `decide`.
-/
import Solutions.Arithmetique.Definitions

/-!
# n² + 3n + 5 et 121

Un classique des olympiades : `n² + 3n + 5` n'est **jamais** divisible par 121.

## Se le représenter
`4(n² + 3n + 5) = (2n + 3)² + 11`. Si 121 divisait le membre de gauche, 11 diviserait `(2n+3)²`,
donc `2n + 3`, donc 121 diviserait `(2n+3)²`… et donc 11 : absurde.

En Lean, on peut aussi écrire `n = 121q + r` et vérifier les 121 restes.

## À prouver
`jamais_121 : (n * n + 3 * n + 5) % 121 ≠ 0`
-/

namespace Parcours.Olymp

theorem jamais_121 (n : Nat) : (n * n + 3 * n + 5) % 121 ≠ 0 := by -- @exo
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 121 ∧ n = 121 * q + r :=
    ⟨n / 121, n % 121, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 121).symm⟩
  have e : (121 * q + r) * (121 * q + r) + 3 * (121 * q + r) + 5 =
      121 * (121 * q * q + 2 * q * r + 3 * q) + (r * r + 3 * r + 5) := by grind
  rw [e, Nat.mul_add_mod]
  clear e
  revert r
  decide

end Parcours.Olymp

#verifier
