/- @parcours
titre: Le dernier chiffre de 7²⁰²⁵
difficulte: 2
requiert: Olympiades.Sept
indice: Récurrence sur `k` : `7^(4(k+1)+1) = 7^(4k+1) × 7⁴` (`Nat.pow_add`), puis `Nat.mul_mod`.
indice: Pour 2025 : réécris d'abord `2025` en `4 * 506 + 1` (`show (2025 : Nat) = 4 * 506 + 1 from rfl`), sinon Lean essaie de calculer `7²⁰²⁵`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Le dernier chiffre de 7²⁰²⁵

Quel est le dernier chiffre de `7²⁰²⁵` (un nombre de 1712 chiffres) ? Les derniers chiffres des
puissances de 7 forment un cycle : `7, 9, 3, 1, 7, 9, 3, 1…` (car `7⁴ = 2401` finit par 1).
Comme `2025 = 4 × 506 + 1`, c'est **7**.

## À prouver
1. `sept_cycle : 7 ^ (4 * k + 1) % 10 = 7`
2. `dernier_chiffre : 7 ^ 2025 % 10 = 7` (sans calculer `7²⁰²⁵` !)
-/

namespace Parcours.Olymp

theorem sept_cycle (k : Nat) : 7 ^ (4 * k + 1) % 10 = 7 := by -- @exo
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 4 * (k + 1) + 1 = (4 * k + 1) + 4 by omega, Nat.pow_add, Nat.mul_mod, ih]

theorem dernier_chiffre : 7 ^ 2025 % 10 = 7 := by -- @exo
  rw [show (2025 : Nat) = 4 * 506 + 1 from rfl]
  exact sept_cycle 506

end Parcours.Olymp

#verifier
