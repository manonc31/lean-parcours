/- @parcours
titre: Pas deux 1 de suite
difficulte: 3
requiert: Combinatoire.Catalan
indice: `induction n using sans11.induct` donne trois cas (0, 1 et `n + 2`) avec deux hypothèses de récurrence.
indice: `fib (n + 4) = fib (n + 2) + fib (n + 3)`.
indice: `tous_bons` : un mot de `sans11 (n + 2)` est `false :: v` ou `true :: false :: v`.
-/
import Solutions.Combinatoire.Definitions

/-!
# Pas deux 1 de suite

Combien de mots binaires de longueur `n` n'ont **jamais deux 1 consécutifs** ? `1, 2, 3, 5, 8,
13…` : les nombres de Fibonacci ! Un tel mot commence par `0` (suivi d'un bon mot de longueur
`n − 1`) ou par `10` (suivi d'un bon mot de longueur `n − 2`).

## À prouver
1. `nombre : (sans11 n).length = fib (n + 2)`
2. `tous_bons` : tous les mots construits n'ont pas deux 1 consécutifs.
3. `tous_la` : pour `n ≤ 10`, on les a tous (en comparant avec tous les mots).
-/

namespace Parcours.Combi

open Parcours.Recurrence

def sans11 : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | n + 2 => (sans11 (n + 1)).map (false :: ·) ++ (sans11 n).map (fun w => true :: false :: w)

def pasDeuxUns : List Bool → Bool
  | [] => true
  | false :: w => pasDeuxUns w
  | [true] => true
  | true :: false :: w => pasDeuxUns w
  | true :: true :: _ => false

def tousMots : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (tousMots n).flatMap fun w => [false :: w, true :: w]

theorem nombre (n : Nat) : (sans11 n).length = fib (n + 2) := by -- @exo
  induction n using sans11.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 =>
    simp only [sans11, List.length_append, List.length_map, ih1, ih2]
    rw [fib_add_two (n + 2), show n + 2 + 1 = n + 1 + 2 from rfl]
    omega

theorem tous_bons (n : Nat) : ∀ w ∈ sans11 n, pasDeuxUns w = true := by -- @exo
  induction n using sans11.induct with
  | case1 => simp [sans11, pasDeuxUns]
  | case2 => simp [sans11, pasDeuxUns]
  | case3 n ih1 ih2 =>
    intro w hw
    simp only [sans11, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · simp only [pasDeuxUns]
      exact ih1 v hv
    · simp only [pasDeuxUns]
      exact ih2 v hv

theorem tous_la : ∀ n, n < 11 → ((tousMots n).filter pasDeuxUns).length = (sans11 n).length := by -- @exo
  decide +kernel

end Parcours.Combi

#verifier
