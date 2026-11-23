/- @parcours
titre: Écrire un nombre en binaire
difficulte: 3
indice: `fun_induction binaire n with` : le cas `n = 0` et le cas récursif.
indice: Cas récursif : `valeur ((n % 2 == 1) :: binaire (n / 2)) = (n % 2 == 1).toNat + 2 * valeur (binaire (n / 2))`. Avec `ih`, il reste `… + 2 * (n / 2) = n`. Distingue `n % 2 = 0` et `n % 2 = 1` pour calculer `(n % 2 == 1).toNat`, puis `omega`.
-/
import Solutions.Circuits.Definitions

/-!
# Écrire un nombre en binaire

L'algorithme : le dernier bit est le reste de la division par 2, et on recommence avec le quotient.
Prouve que c'est correct : relire le nombre binaire redonne le nombre de départ.

## À prouver
`valeur_binaire : valeur (binaire n) = n`
-/

namespace Parcours.Circuits

def binaire (n : Nat) : List Bool :=
  if n = 0 then [] else (n % 2 == 1) :: binaire (n / 2)
termination_by n
decreasing_by omega

-- Essaie : `#eval binaire 6` affiche `[false, true, true]` (6 = 0 + 2 + 4).

theorem valeur_binaire (n : Nat) : valeur (binaire n) = n := by -- @exo
  fun_induction binaire n with
  | case1 => rfl
  | case2 n hn ih =>
    rw [valeur_cons, ih]
    have : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases this with h | h <;> simp [h] <;> omega

end Parcours.Circuits

#verifier
