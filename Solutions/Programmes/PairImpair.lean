/- @parcours
titre: Pair et impair, mutuellement
difficulte: 2
requiert: Programmes.Definitions
indice: Récurrence sur `n` pour la conjonction des deux énoncés.
indice: Puis deux cas : `n % 2 = 0` ou `1` (`Nat.mod_two_eq_zero_or_one`), et `simp`.
-/
import Solutions.Programmes.Definitions

/-!
# Pair et impair, mutuellement

Deux fonctions qui s'appellent l'une l'autre (**récursion mutuelle**) : `n + 1` est pair si `n`
est impair, et impair si `n` est pair.

## À prouver
`pair_impair : estPair n = (n % 2 == 0) ∧ estImpair n = (n % 2 == 1)`

Il faut prouver les deux en même temps : chacune a besoin de l'autre dans la récurrence.
-/

namespace Parcours.Prog

mutual
def estPair : Nat → Bool
  | 0 => true
  | n + 1 => estImpair n

def estImpair : Nat → Bool
  | 0 => false
  | n + 1 => estPair n
end

theorem pair_impair (n : Nat) : estPair n = (n % 2 == 0) ∧ estImpair n = (n % 2 == 1) := by -- @exo
  induction n with
  | zero => simp [estPair, estImpair]
  | succ n ih =>
    simp only [estPair, estImpair, ih.1, ih.2]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (n + 1) % 2 = 0 := by omega
      simp [h, h']

end Parcours.Prog

#verifier
