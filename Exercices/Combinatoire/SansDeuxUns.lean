import Exercices.Combinatoire.Definitions

/-!
# Pas deux 1 de suite

Combien de mots binaires de longueur `n` n'ont **jamais deux 1 consécutifs** ? `1, 2, 3, 5, 8,
13…` : les nombres de Fibonacci ! Un tel mot commence par `0` (suivi d'un bon mot de longueur
`n − 1`) ou par `10` (suivi d'un bon mot de longueur `n − 2`).

## À prouver
1. `nombre : (sans11 n).length = fib (n + 2)`
2. `tous_bons` : tous les mots construits n'ont pas deux 1 consécutifs.
3. `tous_la` : pour `n ≤ 10`, on les a tous (en comparant avec tous les mots).

---
*Exercice* `Combinatoire.SansDeuxUns` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Combinatoire.SansDeuxUns` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

theorem nombre (n : Nat) : (sans11 n).length = fib (n + 2) := by
  sorry

theorem tous_bons (n : Nat) : ∀ w ∈ sans11 n, pasDeuxUns w = true := by
  sorry

theorem tous_la : ∀ n, n < 11 → ((tousMots n).filter pasDeuxUns).length = (sans11 n).length := by
  sorry

end Parcours.Combi

#verifier
