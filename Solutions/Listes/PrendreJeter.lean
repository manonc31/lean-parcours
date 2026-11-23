/- @parcours
titre: Prendre et jeter
difficulte: 3
indice: Récurrence sur `n` en généralisant `l` (`induction n generalizing l`), puis `cases l`.
indice: Les définitions de `prendre` et `jeter` sont par cas sur `n` ET `l` : dans chaque cas, `rfl` ou `show` déplient tout.
indice: `longueur_prendre` : `omega` sait gérer `min`.
-/
import Solutions.Listes.Longueur

/-!
# Prendre et jeter

`prendre n l` : les `n` premiers éléments. `jeter n l` : tout sauf les `n` premiers.

## À prouver
1. `prendre_jeter : prendre n l ++ jeter n l = l`
2. `longueur_prendre : longueur (prendre n l) = min n (longueur l)`
3. `longueur_jeter : longueur (jeter n l) = longueur l - n`
-/

namespace Parcours.Listes.Liste

variable {α : Type}

theorem prendre_jeter (n : Nat) (l : Liste α) : prendre n l ++ jeter n l = l := by -- @exo
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons x l =>
      show x ∷ (prendre n l ++ jeter n l) = x ∷ l
      rw [ih]

theorem longueur_prendre (n : Nat) (l : Liste α) : longueur (prendre n l) = min n (longueur l) := by -- @exo
  induction n generalizing l with
  | zero => exact (Nat.zero_min _).symm
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons x l =>
      show longueur (prendre n l) + 1 = min (n + 1) (longueur l + 1)
      rw [ih]
      omega

theorem longueur_jeter (n : Nat) (l : Liste α) : longueur (jeter n l) = longueur l - n := by -- @exo
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => show 0 = 0 - (n + 1); omega
    | cons x l =>
      show longueur (jeter n l) = longueur l + 1 - (n + 1)
      rw [ih]
      omega

end Parcours.Listes.Liste

#verifier
