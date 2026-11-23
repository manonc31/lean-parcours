/- @parcours
titre: Échauffement de compétition
difficulte: 2
requiert: Arithmetique.Congruences
indice: Raisonne selon le reste de `n` : `have : n % 2 = 0 ∨ n % 2 = 1 := by omega`, puis `rcases this with h | h` et `simp [Nat.mul_mod, Nat.add_mod, h]`.
indice: Pour 3, il y a trois restes possibles ; pour 6, six.
-/
import Solutions.Arithmetique.Definitions

/-!
# Échauffement de compétition

Trois classiques des compétitions, tous résolus par la même technique : **raisonner selon le
reste** de `n` dans une division, et calculer modulo.

## À prouver
1. `produit_consecutifs : (n * (n + 1)) % 2 = 0` (le produit de deux entiers consécutifs est pair)
2. `carre_mod_trois : (n * n) % 3 ≠ 2` (un carré n'est jamais de la forme `3k + 2`)
3. `cube_mod_six : (n * n * n) % 6 = n % 6` (donc 6 divise `n³ − n`)
-/

namespace Parcours.Olymp

theorem produit_consecutifs (n : Nat) : (n * (n + 1)) % 2 = 0 := by -- @exo
  have : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases this with h | h <;> simp [Nat.mul_mod, Nat.add_mod, h]

theorem carre_mod_trois (n : Nat) : (n * n) % 3 ≠ 2 := by -- @exo
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [Nat.mul_mod, h]

theorem cube_mod_six (n : Nat) : (n * n * n) % 6 = n % 6 := by -- @exo
  have : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases this with h | h | h | h | h | h <;> simp [Nat.mul_mod, h]

end Parcours.Olymp

#verifier
