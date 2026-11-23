/- @parcours
titre: Une somme pondérée par les puissances de 2
difficulte: 2
requiert: Classiques.PuissancesTrois
indice: Récurrence ; `somme_succ` et `Nat.pow_succ`, puis `grind`.
-/
import Solutions.Recurrence.Definitions

/-!
# Une somme pondérée par les puissances de 2

## Se le représenter
`0·1 + 1·2 + 2·4 + 3·8 = 34 = 2·16 + 2`. La somme `Σ i·2ⁱ` vaut `(n − 2)·2ⁿ + 2` (c'est le nombre
moyen de comparaisons de certains algorithmes « diviser pour régner »). Sans soustraction :
`somme + 2^(n+1) = n·2ⁿ + 2`.

## À prouver
`poids_binaires : somme (fun i => i * 2 ^ i) n + 2 ^ (n + 1) = n * 2 ^ n + 2`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem poids_binaires (n : Nat) : somme (fun i => i * 2 ^ i) n + 2 ^ (n + 1) = n * 2 ^ n + 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.pow_succ 2 (n + 1), Nat.pow_succ 2 n]
    rw [Nat.pow_succ] at ih
    grind

end Parcours.Classiques

#verifier
