/- @parcours
titre: La suite de Conway
difficulte: 1
requiert: Programmes.Magicien
indice: Les calculs : `decide` / `decide +kernel`.
indice: `longueur_paire` : chaque groupe donne 2 chiffres ; `List.length_flatMap`, puis `List.map_const'` et `List.sum_replicate_nat`.
-/
import Solutions.Programmes.Definitions

/-!
# La suite de Conway

`1 → 11 → 21 → 1211 → 111221 → 312211 → …` : chaque terme **décrit** le précédent à voix haute
(« un 1 », « deux 1 », « un 2, un 1 »…). John Conway a prouvé que la longueur croît d'environ 30 %
à chaque étape, et qu'aucun chiffre plus grand que 3 n'apparaît jamais.

## À prouver
1. `conway : repeter regarder 5 [1] = [3, 1, 2, 2, 1, 1]`
2. `deux_deux : regarder [2, 2] = [2, 2]` (« deux 2 » : un point fixe !)
3. `longueur_paire : (regarder l).length = 2 * (grouper l).length`
4. `pas_de_quatre` : dans les 12 premiers termes, aucun chiffre ne dépasse 3.

## Ressources
- [Suite de Conway (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Conway)
-/

namespace Parcours.Prog

def grouper : List Nat → List (Nat × Nat)
  | [] => []
  | x :: l =>
    match grouper l with
    | (k, y) :: r => if x = y then (k + 1, y) :: r else (1, x) :: (k, y) :: r
    | [] => [(1, x)]

def regarder (l : List Nat) : List Nat := (grouper l).flatMap fun p => [p.1, p.2]

theorem conway : repeter regarder 5 [1] = [3, 1, 2, 2, 1, 1] := by -- @exo
  decide

theorem deux_deux : regarder [2, 2] = [2, 2] := by -- @exo
  decide

theorem longueur_paire (l : List Nat) : (regarder l).length = 2 * (grouper l).length := by -- @exo
  simp only [regarder, List.length_flatMap, List.length_cons, List.length_nil]
  rw [List.map_const', List.sum_replicate_nat, Nat.mul_comm]

theorem pas_de_quatre : ∀ k, k < 12 → ∀ d ∈ repeter regarder k [1], d ≤ 3 := by -- @exo
  decide +kernel

end Parcours.Prog

#verifier
